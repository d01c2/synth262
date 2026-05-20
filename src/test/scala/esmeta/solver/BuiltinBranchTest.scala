package esmeta.solver

import esmeta.ESMetaTest
import esmeta.cfg.{Branch, CFG, Call, Func}
import esmeta.es.util.Coverage
import esmeta.es.util.Coverage.Cond
import esmeta.ir.{EBool, EClo, ICall}
import esmeta.phase.Solve
import scala.collection.mutable.{Map => MMap, Set => MSet, Queue}
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
    var verified = 0

    // collect unique (builtin, branch) pairs — each branch solved once
    val targets: List[(Func, Branch)] = {
      val pairs = {
        val futures = builtins.map { f =>
          Future {
            val reachable = reachableFuncs(List(f))
            targetBranches(reachable).sortBy(_.id).map(f -> _)
          }
        }
        futures.flatMap(Await.result(_, Duration.Inf))
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
        bid: Int,
        status: String,
        js: Option[String],
        elapsed: Long,
        reason: String,
        simplified: Option[List[Formula]],
        blockingAOs: Set[String],
      )

      println(s"  Solving ${targets.size} branches with $nThreads threads...")

      val results = {
        val futures = targets.map { (f, b) =>
          Future {
            val t0 = System.nanoTime()
            val cond = Cond(b, true)
            val candidates =
              try Solve.solve(f, b, cond).take(20).toList
              catch case _: NotImplementedError | _: MatchError => Nil
            val elapsed = System.nanoTime() - t0

            if (candidates.nonEmpty) {
              val hit = candidates.find { js =>
                try {
                  val interp = cov.run(js)
                  interp.touchedCondViews.keys.exists { cv =>
                    cv.cond.branch.id == b.id && cv.cond.cond == true
                  }
                } catch { case _: Throwable => false }
              }
              hit match
                case Some(js) =>
                  BranchResult(
                    f.name,
                    b.id,
                    "ok",
                    Some(js),
                    elapsed,
                    "",
                    None,
                    Set(),
                  )
                case None =>
                  BranchResult(
                    f.name,
                    b.id,
                    "miss",
                    Some(candidates.head),
                    elapsed,
                    "",
                    None,
                    Set(),
                  )
            } else {
              var reason = "unknown"
              var simplifiedGoal: Option[List[Formula]] = None
              var blockingAOs: Set[String] = Set()
              try {
                val interp = SymbolicInterpreter(f, cond, Solver.solve)
                val goals = interp.result
                if (goals.isEmpty)
                  reason =
                    if (interp.contradictionPruned)
                      "contradiction"
                    else "no-goals"
                else {
                  val params = Solve.paramIds(f)
                  val fs = goals.head
                  simplifiedGoal = Some(fs)
                  if (Reify.hasUninterpretableApp(fs))
                    val names = fs.flatMap(Reify.outerAppNames).toSet
                    blockingAOs = names
                    reason = s"uninterp-app(${names.mkString(",")})"
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
        val res = futures.map(Await.result(_, Duration.Inf))
        res
      }

      // aggregate
      var solved = 0
      var unsolved = 0
      var verifyFailed = 0
      var timings = List[(String, Int, Long)]()
      val reasons = MMap[String, Int]()
      for (r <- results) r.status match
        case "ok" =>
          solved += 1; verified += 1
          timings ::= (r.fname, r.bid, r.elapsed)
          println(
            f"  [OK] ${r.fname} Branch[${r.bid}]:T" +
            f" (${r.elapsed / 1000.0}%.0f us)",
          )
          println(s"       js: ${r.js.get}")
        case "miss" =>
          solved += 1; verifyFailed += 1
          timings ::= (r.fname, r.bid, r.elapsed)
          println(
            f"  [MISS] ${r.fname} Branch[${r.bid}]:T" +
            f" (${r.elapsed / 1000.0}%.0f us)",
          )
          println(s"         js: ${r.js.get}")
        case _ =>
          unsolved += 1
          reasons(r.reason) = reasons.getOrElse(r.reason, 0) + 1

      // timing summary
      if (timings.nonEmpty) {
        println(s"\n  Top 10 slowest:")
        for ((name, bid, ns) <- timings.sortBy(-_._3).take(10))
          println(f"    ${ns / 1_000_000.0}%8.2f ms  $name Branch[$bid]")
        val totalMs = timings.map(_._3).sum / 1_000_000.0
        val avgUs = timings.map(_._3).sum / timings.size / 1_000.0
        println(f"\n  Solve time: $totalMs%.1f ms total, $avgUs%.1f us avg")
      }

      val total = targets.size
      println(f"\n  Target branches: $total")
      println(
        f"  Solve rate: $solved / $total (${solved * 100.0 / total}%.1f%%)",
      )
      println(
        f"  Verified:   $verified / $total (${verified * 100.0 / total}%.1f%%)",
      )

      if (reasons.nonEmpty) {
        println(f"\n  Unsolved breakdown:")
        var uninterpTotal = 0
        val aoFreq = MMap[String, Int]()
        val others = List.newBuilder[(String, Int)]
        for ((reason, count) <- reasons.toList.sortBy(-_._2))
          if (reason.startsWith("uninterp-app(")) {
            uninterpTotal += count
            val names = reason.stripPrefix("uninterp-app(").stripSuffix(")")
            for (n <- names.split(","))
              aoFreq(n.trim) = aoFreq.getOrElse(n.trim, 0) + count
          } else others += (reason -> count)
        if (uninterpTotal > 0)
          others += ("uninterp-app" -> uninterpTotal)
        for ((reason, count) <- others.result().sortBy(-_._2))
          println(f"    $count%4d  $reason")
        if (aoFreq.nonEmpty) {
          println(f"\n  Blocking AO frequency (top 30):")
          for ((name, count) <- aoFreq.toList.sortBy(-_._2).take(30))
            println(f"    $count%4d  $name")
        }
      }

      // dump full diagnostics to file
      val dumpFile = new PrintWriter("solve-dump.log")
      try {
        // dump MISS cases
        for (r <- results if r.status == "miss") {
          dumpFile.println(s"=== ${r.fname} Branch[${r.bid}] === MISS")
          dumpFile.println(s"  [js] ${r.js.get}")
          // re-derive the formula for diagnostics
          try {
            val cond = Cond(
              cfg.nodeMap(r.bid).asInstanceOf[Branch],
              true,
            )
            val goals = SymbolicInterpreter(
              cfg.funcs.find(_.name == r.fname).get,
              cond,
              Solver.solve,
            ).result
            goals.headOption.foreach { fs =>
              dumpFile.println("  [simplified]")
              fs.foreach(f => dumpFile.println(s"    $f"))
            }
          } catch { case _: Throwable => () }
          dumpFile.println()
        }
        dumpFile.println("=" * 60)
        // dump unsolved cases
        for (r <- results if r.status == "unsolved") {
          dumpFile.println(s"=== ${r.fname} Branch[${r.bid}] === ${r.reason}")
          r.simplified.foreach { fs =>
            dumpFile.println("  [simplified]")
            fs.foreach(f => dumpFile.println(s"    $f"))
          }
          if (r.blockingAOs.nonEmpty)
            dumpFile.println(s"  [blocking] ${r.blockingAOs.mkString(", ")}")
          dumpFile.println()
        }
      } finally dumpFile.close()
      println(s"\n  Full dump written to solve-dump.log")

      assert(solved > 0)
      assert(verified > 0)
    }

    check("builtin branches: summary") {
      val total = targets.size
      println(
        s"  Builtin functions:  ${builtins.size} (${allBuiltins.size - builtins.size} excluded)",
      )
      println(s"  Target branches:    $total")
      println(
        f"  Total coverage:     $verified/$total" +
        f" (${verified * 100.0 / total}%.1f%%)",
      )
      assert(total > 0)
      pool.shutdown()
    }
  }

  init
}
