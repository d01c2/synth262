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
import java.util.concurrent.Executors
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
    val pool = Executors.newFixedThreadPool(nThreads)
    given ExecutionContext = ExecutionContext.fromExecutor(pool)

    val allBuiltins = cfg.funcs.filter(_.isBuiltin).sortBy(_.name)
    val builtins = {
      val futures = allBuiltins.map { f =>
        Future {
          val ok = Reify.funcAccessExpr(f).exists { js =>
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

    // collect unique (builtin, branch) pairs; each branch is solved once.
    val targets: List[(Func, Branch)] = {
      val pairs = reachableByBuiltin.flatMap {
        case (f, reachable) =>
          targetBranches(reachable).sortBy(_.id).map(f -> _)
      }
      val seen = MSet[Int]()
      val buf = List.newBuilder[(Func, Branch)]
      for ((f, b) <- pairs)
        if (seen.add(b.id)) buf += (f -> b)
      buf.result()
    }

    check("builtin branches: solve and verify") {
      case class BranchResult(
        fname: String,
        targetName: String,
        targetCfg: String,
        bid: Int,
        status: String,
        js: Option[String],
        elapsed: Long,
        reason: String,
        simplified: Option[List[Formula]],
        blockingAOs: Set[String],
      )

      case class Candidate(js: String, simplified: List[Formula])

      println(s"  Solving ${targets.size} branches with $nThreads threads...")

      val results = {
        val futures = targets.map { (f, b) =>
          Future {
            val t0 = System.nanoTime()
            val cond = Cond(b, true)
            val targetFunc = cfg.funcOf(b)
            val candidates =
              try {
                val params = Solve.paramIds(f)
                SymbolicInterpreter(f, cond, Solver.solveAll).result
                  .flatMap { fs =>
                    Reify(fs, params).witness.flatMap { w =>
                      Reify.toJsCall(f, params, w).map(Candidate(_, fs))
                    }
                  }
                  .take(20)
                  .toList
              } catch case _: NotImplementedError | _: MatchError => Nil
            val elapsed = System.nanoTime() - t0

            if (candidates.nonEmpty) {
              val hit = candidates.find { cand =>
                try {
                  val interp = cov.run(cand.js)
                  interp.touchedCondViews.keys.exists { cv =>
                    cv.cond.branch.id == b.id && cv.cond.cond == true
                  }
                } catch { case _: Throwable => false }
              }
              hit match
                case Some(js) =>
                  BranchResult(
                    f.name,
                    targetFunc.name,
                    s"logs/cfg/func/${targetFunc.normalizedName}.cfg",
                    b.id,
                    "ok",
                    Some(js.js),
                    elapsed,
                    "",
                    Some(js.simplified),
                    Set(),
                  )
                case None =>
                  val cand = candidates.head
                  BranchResult(
                    f.name,
                    targetFunc.name,
                    s"logs/cfg/func/${targetFunc.normalizedName}.cfg",
                    b.id,
                    "miss",
                    Some(cand.js),
                    elapsed,
                    "",
                    Some(cand.simplified),
                    Set(),
                  )
            } else {
              var reason = "unknown"
              var simplifiedGoal: Option[List[Formula]] = None
              var blockingAOs: Set[String] = Set()
              try {
                val interp =
                  SymbolicInterpreter(f, cond, Solver.solveAll)
                val goals = interp.result
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
                  simplifiedGoal = Some(fs)
                  if (Reify.hasUninterpretableApp(fs))
                    val names = fs.flatMap(Reify.outerAppNames).toSet
                    blockingAOs = names
                    reason =
                      s"uninterp-app(${names.toList.sorted.mkString(",")})"
                  else
                    Reify(fs, params).witness match
                      case None =>
                        reason = "reify-failed"
                      case Some(w) =>
                        Reify.toJsCall(f, params, w) match
                          case None    => reason = "no-js-call"
                          case Some(_) => reason = "unknown"
                }
              } catch {
                case e: NotImplementedError =>
                  val site = e.getStackTrace.headOption
                    .map(_.getMethodName)
                    .getOrElse("?")
                  reason = s"unimpl($site)"
                case e: MatchError =>
                  reason = s"missing-transfer(${e.getMessage.take(60)})"
                case e: Throwable =>
                  reason = s"error(${e.getClass.getSimpleName})"
              }
              BranchResult(
                f.name,
                targetFunc.name,
                s"logs/cfg/func/${targetFunc.normalizedName}.cfg",
                b.id,
                "unsolved",
                None,
                elapsed,
                reason,
                simplifiedGoal,
                blockingAOs,
              )
            }
          }
        }
        futures.map(Await.result(_, Duration.Inf))
      }

      val verifiedResults = results.filter(_.status == "ok")
      val missedResults = results.filter(_.status == "miss")
      val unsolvedResults =
        results.filter(r => r.status != "ok" && r.status != "miss")
      val solved = verifiedResults.size + missedResults.size
      val verified = verifiedResults.size
      val verifyFailed = missedResults.size
      val timings =
        (verifiedResults ++ missedResults).map(r => (r.fname, r.bid, r.elapsed))
      val reasons =
        unsolvedResults.groupMapReduce(_.reason)(_ => 1)(_ + _)
      val blockingAoFreq =
        results.flatMap(_.blockingAOs).groupMapReduce(identity)(_ => 1)(_ + _)

      for (r <- missedResults)
        println(
          f"  [MISS] ${r.fname} Branch[${r.bid}]:T" +
          f" (${r.elapsed / 1000.0}%.0f us)",
        )

      // timing summary
      if (timings.nonEmpty) {
        println(s"\n  Top 10 slowest:")
        for ((name, bid, ns) <- timings.sortBy(-_._3).take(10))
          println(f"    ${ns / 1_000_000.0}%8.2f ms  $name Branch[$bid]")
        val totalMs = timings.map(_._3).sum / 1_000_000.0
        val avgUs = timings.map(_._3).sum / timings.size / 1_000.0
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
            s"=== ${r.fname} -> ${r.targetName} Branch[${r.bid}] === ${r.status.toUpperCase}",
          )
          dumpFile.println(s"  [cfg] ${r.targetCfg}")
          r.js.foreach(js => dumpFile.println(s"  [js] $js"))
          r.simplified.foreach { fs =>
            dumpFile.println("  [simplified]")
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
            s"=== ${r.fname} -> ${r.targetName} Branch[${r.bid}] === ${r.reason}",
          )
          dumpFile.println(s"  [cfg] ${r.targetCfg}")
          r.simplified.foreach { fs =>
            dumpFile.println("  [simplified]")
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
      val missRate = if (solved == 0) 0.0 else verifyFailed * 100.0 / solved
      println(
        s"\n  Builtin functions:  ${builtins.size} (${allBuiltins.size - builtins.size} excluded)",
      )
      println(f"  Target branches: $total")
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
      pool.shutdown()
    }
  }

  init
}
