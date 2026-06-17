package esmeta.solver

import esmeta.ESMetaTest
import esmeta.cfg.{Branch, CFG, Call, Func}
import esmeta.es.util.Coverage
import esmeta.es.util.Coverage.Cond
import esmeta.ty.ValueTy
import esmeta.ir.{EBool, EClo, ICall}
import esmeta.phase.Solve
import scala.collection.mutable.{Set => MSet, Queue}
import scala.concurrent.{Future, Await, ExecutionContext}
import scala.concurrent.duration.Duration
import java.util.concurrent.{
  Callable,
  ExecutorCompletionService,
  Executors,
  ThreadFactory,
  TimeUnit,
  TimeoutException,
}
import java.io.PrintWriter

class CoverageMiddleTest extends SolverTest {
  val name = "solverCovTest"

  lazy val cfg = ESMetaTest.cfg

  /** coverage-style branch filter: exclude compiler boilerplate */
  private def isTargetBranch(b: Branch): Boolean =
    !b.isFiltered && (b.cond match
      case EBool(_) => false
      case _        => true
    )

  /** static callees: resolve EClo targets in Call nodes */
  private def directCallees(f: Func): Set[Func] =
    f.nodes.collect { case c: Call => c.callInst }.flatMap {
      case ICall(_, EClo(name, _), _) => cfg.fnameMap.get(name)
      case _                          => None
    }

  /** transitive closure of callees from root functions */
  private def reachableFuncs(roots: List[Func]): Set[Func] =
    val visited = MSet.from(roots.map(_.id))
    val queue = Queue.from(roots)
    while (queue.nonEmpty)
      for
        callee <- directCallees(queue.dequeue())
        if visited.add(callee.id)
      do queue.enqueue(callee)
    visited.flatMap(cfg.funcMap.get).toSet

  private def targetBranches(fs: Iterable[Func]): List[Branch] =
    fs.flatMap(_.nodes.collect { case b: Branch if isTargetBranch(b) => b })
      .toList

  def init: Unit = {
    given CFG = cfg
    val cov = Coverage(cfg, timeLimit = Some(10))
    val solveTimeLimit = 5
    val solveTimeout = Duration(solveTimeLimit, "seconds")
    val runner = SymInterp(cfg, timeLimit = Some(solveTimeLimit))
    val allBuiltins = cfg.funcs.filter(_.isBuiltin).sortBy(_.name)

    val nThreads = Runtime.getRuntime.availableProcessors
    val pool = Executors.newFixedThreadPool(
      nThreads,
      new ThreadFactory {
        private var nextId = 0
        def newThread(r: Runnable): Thread = {
          nextId += 1
          val t = new Thread(r, s"builtin-branch-test-$nextId")
          t.setDaemon(true)
          t
        }
      },
    )
    given ExecutionContext = ExecutionContext.fromExecutor(pool)
    val builtins = {
      val futures = allBuiltins.map { f =>
        Future {
          val ok = Solver.funcAccessExpr(f).exists { js =>
            try { cov.run(js + ".call();").supported }
            catch { case _: Throwable => false }
          }
          if (ok) Some(f) else None
        }
      }
      futures.flatMap(Await.result(_, Duration.Inf))
    }
    val reachableByBuiltin: List[(Func, Set[Func])] = {
      val futures = builtins.map { f =>
        Future(f -> reachableFuncs(List(f)))
      }
      futures.map(Await.result(_, Duration.Inf)).toList
    }
    val builtinEntries = builtins.toSet
    val reachableModelingAOs = reachableByBuiltin.flatMap(_._2).toSet
    val builtinEntryAONames = builtinEntries.map(_.name).toList.sorted
    val nonEntryAONames =
      (reachableModelingAOs -- builtinEntries).map(_.name).toList.sorted
    val modelingAOCount = reachableModelingAOs.size

    // collect unique branches; entry selection via reverse call graph
    // (matches `sbt run solve` so miss cases are reproducible)
    val accessibleBuiltins = builtins.toSet
    val funcEntryCache = collection.mutable.Map[Int, List[Func]]()
    def entriesFor(b: Branch): List[Func] =
      funcEntryCache.getOrElseUpdate(
        cfg.funcOf(b).id,
        SymInterp.sortedEntries(b).filter(accessibleBuiltins.contains),
      )
    val targetBranchEntries: List[(Func, Branch)] = {
      val seen = MSet[Int]()
      val buf = List.newBuilder[(Func, Branch)]
      for {
        (_, reachable) <- reachableByBuiltin
        b <- targetBranches(reachable).sortBy(_.id)
        if seen.add(b.id)
        entries = entriesFor(b)
        if entries.nonEmpty
      } buf += (entries.head -> b)
      buf.result()
    }
    val targets: List[(Func, Cond)] =
      targetBranchEntries.flatMap { (f, b) =>
        List(f -> Cond(b, true), f -> Cond(b, false))
      }

    check("builtin branches: solve and verify") {
      case class BranchResult(
        fname: String,
        targetName: String,
        targetCfg: String,
        bid: Int,
        side: Boolean,
        status: String,
        js: Option[String],
        elapsed: Long,
        path: Option[List[Cond]],
        calls: Option[List[Call]],
        saturated: Option[Map[Int, ValueTy]],
      )

      def sideString(side: Boolean): String = if (side) "T" else "F"

      println(
        s"  Solving ${targets.size} branch sides from " +
        s"${targetBranchEntries.size} branches with $nThreads threads " +
        s"(timeout: $solveTimeout per side)...",
      )

      val results = {
        def timeoutResult(f: Func, cond: Cond): BranchResult = {
          val b = cond.branch
          val targetFunc = cfg.funcOf(b)
          BranchResult(
            f.name,
            targetFunc.name,
            s"logs/cfg/func/${targetFunc.normalizedName}.cfg",
            b.id,
            cond.cond,
            "timeout",
            None,
            solveTimeout.toNanos,
            None,
            None,
            None,
          )
        }

        def solveTarget(f: Func, cond: Cond): BranchResult = {
          val t0 = System.nanoTime()
          val interp = runner(f, cond)
          def checkTimeout(): Unit =
            if (interp.timeout) throw TimeoutException("solver")
          def elapsedNanos: Long = System.nanoTime() - t0
          val b = cond.branch
          val targetFunc = cfg.funcOf(b)
          Thread
            .currentThread()
            .setName(
              s"builtin-branch-test ${f.name} " +
              s"Branch[${b.id}]:${sideString(cond.cond)}",
            )

          def verifies(js: String): Boolean =
            checkTimeout()
            try {
              val interp = cov.run(js)
              checkTimeout()
              interp.touchedCondViews.keys.exists { cv =>
                cv.cond.branch.id == b.id && cv.cond.cond == cond.cond
              }
            } catch {
              case e: TimeoutException => throw e
              case _: Throwable        => false
            }

          try {
            interp.result match {
              case Some(conf) =>
                interp.reify match
                  case Some(js) =>
                    if (verifies(js))
                      BranchResult(
                        f.name,
                        targetFunc.name,
                        s"logs/cfg/func/${targetFunc.normalizedName}.cfg",
                        b.id,
                        cond.cond,
                        "pass",
                        Some(js),
                        elapsedNanos,
                        Some(conf.path),
                        Some(conf.calls),
                        Some(conf.state.symEnv),
                      )
                    else
                      BranchResult(
                        f.name,
                        targetFunc.name,
                        s"logs/cfg/func/${targetFunc.normalizedName}.cfg",
                        b.id,
                        cond.cond,
                        "fail-verify",
                        Some(js),
                        elapsedNanos,
                        Some(conf.path),
                        Some(conf.calls),
                        Some(conf.state.symEnv),
                      )
                  case None =>
                    BranchResult(
                      f.name,
                      targetFunc.name,
                      s"logs/cfg/func/${targetFunc.normalizedName}.cfg",
                      b.id,
                      cond.cond,
                      "fail-reify",
                      None,
                      elapsedNanos,
                      Some(conf.path),
                      Some(conf.calls),
                      Some(conf.state.symEnv),
                    )
              case None =>
                // symbolic execution returned no model: distinguish a genuine
                // "unsolved" from one aborted by the per-side time limit
                BranchResult(
                  f.name,
                  targetFunc.name,
                  s"logs/cfg/func/${targetFunc.normalizedName}.cfg",
                  b.id,
                  cond.cond,
                  if (interp.timeout) "timeout" else "unsolved",
                  None,
                  elapsedNanos,
                  None,
                  None,
                  None,
                )
            }
          } catch {
            case _: TimeoutException => timeoutResult(f, cond)
          }
        }

        val completion = ExecutorCompletionService[BranchResult](pool)
        val targetIter = targets.iterator
        val resultBuilder = List.newBuilder[BranchResult]
        var submitted = 0
        var completed = 0

        def submitNext(): Unit =
          if (targetIter.hasNext) {
            val (f, cond) = targetIter.next()
            completion.submit(new Callable[BranchResult] {
              def call(): BranchResult = solveTarget(f, cond)
            })
            submitted += 1
          }

        for (_ <- 0 until math.min(nThreads, targets.size)) submitNext()

        while (completed < targets.size) {
          val done = completion.poll(30, TimeUnit.SECONDS)
          if (done == null) {
            println(
              s"  progress: $completed / ${targets.size} completed " +
              s"($submitted submitted)",
            )
            // diagnostic: dump where the in-flight worker threads are stuck
            import scala.jdk.CollectionConverters.*
            for {
              (t, stack) <- Thread.getAllStackTraces.asScala.toList
              if t.getName.startsWith("builtin-branch-test")
            } {
              println(s"  [stuck] ${t.getName}")
              for (frame <- stack.take(20))
                println(s"      at $frame")
            }
          } else {
            resultBuilder += done.get()
            completed += 1
            submitNext()
          }
        }
        resultBuilder.result().sortBy(r => (r.bid, if (r.side) 0 else 1))
      }

      val verifiedResults = results.filter(_.status == "pass")
      val missedResults = results.filter(_.status == "fail-verify")
      val solved = verifiedResults.size + missedResults.size
      val verified = verifiedResults.size
      val timings =
        (verifiedResults ++ missedResults)
          .map(r => (r.fname, r.bid, r.side, r.elapsed))

      val statusOrder =
        List("pass", "fail-verify", "fail-reify", "unsolved", "timeout")
      val byStatus = results.groupBy(_.status)
      val orderedStatuses =
        statusOrder.filter(byStatus.contains) ++
        byStatus.keys.filterNot(statusOrder.contains).toList.sorted

      // emit the run summary to an arbitrary sink (console and/or dump file)
      def writeReport(out: String => Unit): Unit = {
        // per-status breakdown: count, share, and elapsed time per status tag
        val totalCount = results.size
        out("\n  Status breakdown:")
        for (status <- orderedStatuses) {
          val rs = byStatus(status)
          val totalS = rs.map(_.elapsed).sum / 1e9
          val avgS = totalS / rs.size
          val pct = if (totalCount == 0) 0.0 else rs.size * 100.0 / totalCount
          out(
            f"    $status%-12s ${rs.size}%5d (${pct}%5.1f%%)  " +
            f"(total $totalS%8.1fs, avg $avgS%6.3fs)",
          )
        }
        val grandTotalS = results.map(_.elapsed).sum / 1e9
        out(
          f"    ${"total"}%-12s $totalCount%5d (100.0%%)  " +
          f"(total $grandTotalS%8.1fs)",
        )
        // timing summary
        if (timings.nonEmpty) {
          out("\n  Top 10 slowest:")
          for ((name, bid, side, ns) <- timings.sortBy(-_._4).take(10))
            out(
              f"    ${ns / 1e9}%8.3fs  " +
              s"$name Branch[$bid]:${sideString(side)}",
            )
          val totalS = timings.map(_._4).sum / 1e9
          val avgS = totalS / timings.size
          out(f"\n  Solve time: $totalS%.1fs total, $avgS%.3fs avg")
        }
        out("\n  Modeling AO targets:")
        out(f"    total unique:  $modelingAOCount%4d")
        out(f"    entry:         ${builtinEntryAONames.size}%4d")
        out(f"    non-entry:     ${nonEntryAONames.size}%4d")
      }

      writeReport(s => println(s))

      // dump full diagnostics to file
      val dumpFile = new PrintWriter("solve-dump.log")
      def section(title: String): Unit = {
        dumpFile.println()
        dumpFile.println("=" * 72)
        dumpFile.println(s"  $title")
        dumpFile.println("=" * 72)
      }
      try {
        // (1) run summary, identical to the console output
        section("RUN SUMMARY")
        writeReport(s => dumpFile.println(s))

        // (2) modeling AO names (counts already shown in the summary above)
        section("MODELING AO NAMES")
        dumpFile.println(s"\n  [entry] ${builtinEntryAONames.size}")
        builtinEntryAONames.foreach(name => dumpFile.println(s"    $name"))
        dumpFile.println(s"\n  [non-entry] ${nonEntryAONames.size}")
        nonEntryAONames.foreach(name => dumpFile.println(s"    $name"))

        // (3) per-case detail, grouped by status, slowest first within a group
        def dumpCase(r: BranchResult): Unit = {
          val path =
            if (r.fname == r.targetName) r.fname
            else s"${r.fname} -> ${r.targetName}"
          dumpFile.println(
            f"[${r.status.toUpperCase}] $path  " +
            f"Branch[${r.bid}]:${sideString(r.side)}" +
            f"  (${r.elapsed / 1e9}%.3fs)",
          )
          dumpFile.println(s"    cfg: ${r.targetCfg}")
          r.js.foreach(js => dumpFile.println(s"    js:  $js"))
          r.path.foreach(ps =>
            val ss = ps.map(c => s"${c.branch.id}:${sideString(c.cond)}")
            dumpFile.println(s"    path: [${ss.size}] ${ss.mkString(" <- ")}"),
          )
          r.calls.foreach(cs =>
            val ss = cs.map(c =>
              c.callInst match
                case ICall(_, EClo(name, _), _) => s"${c.id}:$name"
                case _                          => s"${c.id}",
            )
            dumpFile.println(s"    calls: [${ss.size}] ${ss.mkString(" <- ")}"),
          )
          r.saturated.filter(_.nonEmpty).foreach { fs =>
            dumpFile.println("    saturated:")
            fs.toList
              .sortBy(_._1)
              .foreach { (k, v) =>
                val x = k match
                  case -1 => "#THIS"
                  case -2 => "#ARGS"
                  case -3 => "#NEW_TARGET"
                  case i  => s"#$i"
                dumpFile.println(s"      $x -> $v")
              }
          }
          dumpFile.println()
        }
        for (status <- orderedStatuses) {
          val rs = byStatus(status).sortBy(-_.elapsed)
          section(f"${status.toUpperCase} (${rs.size})")
          dumpFile.println()
          rs.foreach(dumpCase)
        }
      } finally dumpFile.close()
      println(s"\n  Full dump written to solve-dump.log")

      assert(solved > 0)
      assert(verified > 0)
    }

    check("builtin branches: summary") {
      val total = targets.size
      assert(total > 0)
      pool.shutdownNow()
    }
  }

  init
}
