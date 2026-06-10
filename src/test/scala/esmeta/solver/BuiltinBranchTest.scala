package esmeta.solver

import esmeta.ESMetaTest
import esmeta.cfg.{Branch, CFG, Call, Func}
import esmeta.es.util.Coverage
import esmeta.es.util.Coverage.Cond
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

class BuiltinBranchTest extends ESMetaTest {
  val name = "builtinBranchTest"
  val category = "solver"

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
    val solveTimeLimit = 120
    val solveTimeout = Duration(solveTimeLimit, "seconds")

    val allBuiltins = cfg.funcs.filter(_.isBuiltin).sortBy(_.name)
    val builtins = {
      val futures = allBuiltins.map { f =>
        Future {
          val ok = Reifier.funcAccessExpr(f).exists { js =>
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
        Solve.findEntries(b).filter(accessibleBuiltins.contains),
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
        reason: String,
        saturated: Option[List[Formula]],
        blockingAOs: Set[String],
      )

      case class Candidate(js: String, saturated: List[Formula])

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
            "unsolved",
            None,
            solveTimeout.toNanos,
            "timeout",
            None,
            Set(),
          )
        }

        def solveTarget(f: Func, cond: Cond): BranchResult = {
          val t0 = System.nanoTime()
          val solver = Solver(timeLimit = Some(solveTimeLimit))
          def checkTimeout(): Unit =
            if (solver.timeout) throw TimeoutException("solver")
          def elapsedNanos: Long = System.nanoTime() - t0
          def solveAllTimed(goal: List[Formula]): LazyList[List[Formula]] =
            solver.solveAll(goal)
          val b = cond.branch
          val targetFunc = cfg.funcOf(b)
          Thread
            .currentThread()
            .setName(
              s"builtin-branch-test ${f.name} " +
              s"Branch[${b.id}]:${sideString(cond.cond)}",
            )

          def candidatesFor(entry: Func): LazyList[Candidate] =
            val params = Solve.paramIds(entry)
            SymbolicInterpreter(
              entry,
              cond,
              solveAllTimed,
              solver.hasContradiction,
            ).result
              .flatMap { fs =>
                checkTimeout()
                Reifier(entry, fs, params).map(Candidate(_, fs))
              }
              .take(20)

          def verifies(cand: Candidate): Boolean =
            checkTimeout()
            try {
              val interp = cov.run(cand.js)
              checkTimeout()
              interp.touchedCondViews.keys.exists { cv =>
                cv.cond.branch.id == b.id && cv.cond.cond == cond.cond
              }
            } catch {
              case e: TimeoutException => throw e
              case _: Throwable        => false
            }

          def firstCandidateAndHit(
            entry: Func,
          ): (Option[Candidate], Option[Candidate]) =
            var first: Option[Candidate] = None
            var hit: Option[Candidate] = None
            try {
              val it = candidatesFor(entry).iterator
              while (hit.isEmpty && it.hasNext) {
                checkTimeout()
                val cand = it.next()
                if (first.isEmpty) first = Some(cand)
                if (verifies(cand)) hit = Some(cand)
              }
            } catch {
              case _: NotImplementedError | _: MatchError => ()
            }
            (first, hit)

          try {
            val (firstCandidate, primaryHit) = firstCandidateAndHit(f)
            checkTimeout()

            primaryHit match
              case Some(js) =>
                BranchResult(
                  f.name,
                  targetFunc.name,
                  s"logs/cfg/func/${targetFunc.normalizedName}.cfg",
                  b.id,
                  cond.cond,
                  "ok",
                  Some(js.js),
                  elapsedNanos,
                  "",
                  Some(js.saturated),
                  Set(),
                )
              case None if firstCandidate.nonEmpty =>
                // miss — try remaining entries from reverse call graph.
                val fallbackEntries = entriesFor(b)
                  .filterNot(_.name == f.name)
                val fallbackHit = fallbackEntries.iterator
                  .flatMap { altF =>
                    checkTimeout()
                    val (_, hit) = firstCandidateAndHit(altF)
                    hit.map(js => (altF, js))
                  }
                  .nextOption()
                checkTimeout()
                fallbackHit match
                  case Some((altF, js)) =>
                    BranchResult(
                      altF.name,
                      targetFunc.name,
                      s"logs/cfg/func/${targetFunc.normalizedName}.cfg",
                      b.id,
                      cond.cond,
                      "ok",
                      Some(js.js),
                      elapsedNanos,
                      "",
                      Some(js.saturated),
                      Set(),
                    )
                  case None =>
                    val cand = firstCandidate.get
                    BranchResult(
                      f.name,
                      targetFunc.name,
                      s"logs/cfg/func/${targetFunc.normalizedName}.cfg",
                      b.id,
                      cond.cond,
                      "miss",
                      Some(cand.js),
                      elapsedNanos,
                      "",
                      Some(cand.saturated),
                      Set(),
                    )
              case None =>
                var reason = "unknown"
                var saturatedGoal: Option[List[Formula]] = None
                var blockingAOs: Set[String] = Set()
                try {
                  val interp =
                    SymbolicInterpreter(
                      f,
                      cond,
                      solveAllTimed,
                      solver.hasContradiction,
                    )
                  val goals = interp.result
                  checkTimeout()
                  if (goals.isEmpty)
                    reason =
                      if (interp.targetContradiction) "contradiction"
                      else if (interp.pathContradiction) "pruned"
                      else if (interp.notImplBlocked.isDefined)
                        s"no-goals(${interp.notImplBlocked.get})"
                      else if (interp.loopBlocked) "no-goals(loop)"
                      else if (interp.cycleBlocked) "no-goals(cycle)"
                      else if (interp.stepInBlocked) "no-goals(step-in)"
                      else if (interp.hasVariadic) "no-goals(variadic)"
                      else if (interp.internalMethodDispatch)
                        "no-goals(internal-method)"
                      else "no-goals"
                  else {
                    val params = Solve.paramIds(f)
                    val fs = goals.head
                    saturatedGoal = Some(fs)
                    if (Solver.hasUninterpretableApp(fs))
                      val names = fs.flatMap(Solver.outerAppNames).toSet
                      blockingAOs = names
                      reason =
                        s"uninterp-app(${names.toList.sorted.mkString(",")})"
                    else
                      Reifier(f, fs, params) match
                        case None    => reason = "reify-failed"
                        case Some(_) => reason = "unknown"
                      checkTimeout()
                  }
                } catch {
                  case e: NotImplementedError =>
                    val site = e.getStackTrace.headOption
                      .map(_.getMethodName)
                      .getOrElse("?")
                    reason = s"unimpl($site)"
                  case e: MatchError =>
                    reason = s"missing-transfer(${e.getMessage.take(60)})"
                  case e: TimeoutException =>
                    throw e
                  case e: Throwable =>
                    reason = s"error(${e.getClass.getSimpleName})"
                }
                BranchResult(
                  f.name,
                  targetFunc.name,
                  s"logs/cfg/func/${targetFunc.normalizedName}.cfg",
                  b.id,
                  cond.cond,
                  "unsolved",
                  None,
                  elapsedNanos,
                  reason,
                  saturatedGoal,
                  blockingAOs,
                )
          } catch {
            case _: TimeoutException =>
              timeoutResult(f, cond)
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
          } else {
            resultBuilder += done.get()
            completed += 1
            submitNext()
          }
        }
        resultBuilder.result().sortBy(r => (r.bid, if (r.side) 0 else 1))
      }

      val verifiedResults = results.filter(_.status == "ok")
      val missedResults = results.filter(_.status == "miss")
      val unsolvedResults =
        results.filter(r => r.status != "ok" && r.status != "miss")
      val solved = verifiedResults.size + missedResults.size
      val verified = verifiedResults.size
      val verifyFailed = missedResults.size
      val timings =
        (verifiedResults ++ missedResults)
          .map(r => (r.fname, r.bid, r.side, r.elapsed))
      val reasons =
        unsolvedResults.groupMapReduce(_.reason)(_ => 1)(_ + _)
      val blockingAoFreq =
        results.flatMap(_.blockingAOs).groupMapReduce(identity)(_ => 1)(_ + _)

      for (r <- missedResults)
        println(
          f"  [MISS] ${r.fname} Branch[${r.bid}]:${sideString(r.side)}" +
          f" (${r.elapsed / 1000.0}%.0f us)",
        )

      // timing summary
      if (timings.nonEmpty) {
        println(s"\n  Top 10 slowest:")
        for ((name, bid, side, ns) <- timings.sortBy(-_._4).take(10))
          println(
            f"    ${ns / 1_000_000.0}%8.2f ms  " +
            s"$name Branch[$bid]:${sideString(side)}",
          )
        val totalMs = timings.map(_._4).sum / 1_000_000.0
        val avgUs = timings.map(_._4).sum / timings.size / 1_000.0
        println(f"\n  Solve time: $totalMs%.1f ms total, $avgUs%.1f us avg")
      }

      if (reasons.nonEmpty) {
        println(f"\n  Unsolved breakdown:")
        val uninterpTotal = reasons.iterator.collect {
          case (reason, count) if reason.startsWith("uninterp-app(") => count
        }.sum
        val reasonSummary =
          reasons.toList.filterNot(_._1.startsWith("uninterp-app(")) ++
          Option.when(uninterpTotal > 0)("uninterp-app" -> uninterpTotal)
        for ((reason, count) <- reasonSummary.sortBy(-_._2))
          println(f"    $count%4d  $reason")
      }

      println(f"\n  Modeling AO targets:")
      println(f"    total unique:  $modelingAOCount%4d")
      println(f"    entry:         ${builtinEntryAONames.size}%4d")
      println(f"    non-entry:     ${nonEntryAONames.size}%4d")

      if (blockingAoFreq.nonEmpty) {
        println(f"\n  Blocking AO frequency (top 30):")
        for (
          (name, count) <- blockingAoFreq.toList
            .sortBy((name, count) => (-count, name))
            .take(30)
        )
          println(f"    $count%4d  $name")
      }

      // dump full diagnostics to file
      val dumpFile = new PrintWriter("solve-dump.log")
      try {
        dumpFile.println("=" * 60)
        dumpFile.println("Modeling AO targets")
        dumpFile.println(s"  total unique: $modelingAOCount")
        dumpFile.println(s"  entry: ${builtinEntryAONames.size}")
        dumpFile.println(s"  non-entry: ${nonEntryAONames.size}")
        dumpFile.println(s"  [entry] ${builtinEntryAONames.size}")
        builtinEntryAONames.foreach(name => dumpFile.println(s"    $name"))
        dumpFile.println(s"  [non-entry] ${nonEntryAONames.size}")
        nonEntryAONames.foreach(name => dumpFile.println(s"    $name"))
        dumpFile.println()

        if (blockingAoFreq.nonEmpty) {
          dumpFile.println("=" * 60)
          dumpFile.println(s"Blocking AO frequency ${blockingAoFreq.size}")
          for (
            (name, count) <- blockingAoFreq.toList
              .sortBy((name, count) => (-count, name))
          )
            dumpFile.println(f"    $count%4d  $name")
        }
        dumpFile.println()

        def dumpSolved(r: BranchResult): Unit = {
          dumpFile.println(
            s"=== ${r.fname} -> ${r.targetName} " +
            s"Branch[${r.bid}]:${sideString(r.side)} " +
            s"=== ${r.status.toUpperCase}",
          )
          dumpFile.println(s"  [cfg] ${r.targetCfg}")
          r.js.foreach(js => dumpFile.println(s"  [js] $js"))
          r.saturated.foreach { fs =>
            dumpFile.println("  [saturated]")
            fs.foreach(f => dumpFile.println(s"    $f"))
          }
          dumpFile.println()
        }
        // dump solved cases, including both verified OK and verification MISS.
        for (r <- results if r.status == "ok" || r.status == "miss")
          dumpSolved(r)

        dumpFile.println("=" * 60)
        // dump unsolved cases
        for (r <- results if r.status == "unsolved") {
          dumpFile.println(
            s"=== ${r.fname} -> ${r.targetName} " +
            s"Branch[${r.bid}]:${sideString(r.side)} === ${r.reason}",
          )
          dumpFile.println(s"  [cfg] ${r.targetCfg}")
          r.saturated.foreach { fs =>
            dumpFile.println("  [saturated]")
            fs.foreach(f => dumpFile.println(s"    $f"))
          }
          if (r.blockingAOs.nonEmpty)
            dumpFile.println(
              s"  [blocking] ${r.blockingAOs.toList.sorted.mkString(", ")}",
            )
          dumpFile.println()
        }
      } finally dumpFile.close()
      println(s"\n  Full dump written to solve-dump.log")

      val total = targets.size
      val targetBranches = targetBranchEntries.size
      val missRate = if (solved == 0) 0.0 else verifyFailed * 100.0 / solved
      println(
        s"\n  Builtin functions:  ${builtins.size} (${allBuiltins.size - builtins.size} excluded)",
      )
      println(f"  Target branches: $targetBranches")
      println(f"  Target branch sides: $total")
      println(
        f"  Solve rate: $solved / $total (${solved * 100.0 / total}%.1f%%)",
      )
      println(
        f"  Verified:   $verified / $total (${verified * 100.0 / total}%.1f%%)",
      )
      println(
        f"  Misses:     $verifyFailed / $solved ($missRate%.1f%%)",
      )

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
