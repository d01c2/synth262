package esmeta.solver

import esmeta.ESMetaTest
import esmeta.cfg.{Branch, Call, Func}
import esmeta.es.util.Coverage
import esmeta.es.util.Coverage.Cond
import esmeta.ir.{EBool, EClo, ICall}
import esmeta.phase.Solve
import esmeta.spec.{BuiltinHead, BuiltinPath}
import scala.collection.mutable.{Set => MSet, Queue}

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
    val cov = Coverage(cfg, timeLimit = Some(10))

    val allBuiltins = cfg.funcs
      .filter { f =>
        f.isBuiltin && f.head.exists {
          case BuiltinHead(BuiltinPath.YetPath(_), _, _) => false
          case _: BuiltinHead                            => true
          case _                                         => false
        }
      }
      .sortBy(_.name)
    // probe each builtin: call with no args, exclude if unsupported or throws
    val builtins = allBuiltins.filter { f =>
      Reify.funcAccessExpr(f).exists { js =>
        try { cov.run(js + ".call();").supported }
        catch { case _: Throwable => false }
      }
    }
    val allReachable = reachableFuncs(builtins)
    val helpers = (allReachable -- builtins).toList.sortBy(_.name)

    var verified = 0

    check("builtin branches: solve and verify") {
      // counters
      var loopBlocked = 0
      var yetBlocked = 0
      var missingTransfer = 0
      var appBlocked = 0
      var reifyFail = 0
      var solved = 0
      var verifyFailed = 0
      var timings = List[(String, Int, Long)]()

      for (f <- builtins) {
        val tgt = targetBranches(List(f))
        for (b <- tgt.sortBy(_.id)) {
          val t0 = System.nanoTime()
          val cond = Cond(b, true)

          val candidates =
            try { Solve.solve(f, b, cond) }
            catch { case _: NotImplementedError | _: MatchError => Nil }

          // try each candidate until one verifies
          def tryVerify(js: String): Boolean =
            try {
              val interp = cov.run(js)
              interp.touchedCondViews.keys.exists { cv =>
                cv.cond.branch.id == b.id && cv.cond.cond == true
              }
            } catch { case _: Throwable => false }

          candidates.headOption match
            case Some(_) =>
              solved += 1
              val hit = candidates.find(tryVerify)
              val elapsed = System.nanoTime() - t0
              timings ::= (f.name, b.id, elapsed)
              hit match
                case Some(js) =>
                  verified += 1
                  println(
                    f"  [OK] ${f.name} Branch[${b.id}]:T (${elapsed / 1000.0}%.0f us)",
                  )
                  println(s"       js: $js")
                case None =>
                  val js = candidates.head
                  verifyFailed += 1
                  println(
                    f"  [MISS] ${f.name} Branch[${b.id}]:T (${elapsed / 1000.0}%.0f us)",
                  )
                  println(
                    s"         js: $js (tried ${candidates.size} candidates)",
                  )
                  // debug: show goals for MISS cases
                  val cond0 = Cond(b, true)
                  val paths0 = PathEnumerator(f, b)
                  val goals0 =
                    paths0.flatMap(p => SymbolicInterpreter(f, p, cond0)).toList
                  for ((g, i) <- goals0.zipWithIndex) {
                    val rw = Solver.rewriteApps(g)
                    println(s"         goal[$i]: ${rw.mkString(" /\\ ")}")
                  }
            case None =>
              // diagnose failure reason
              val paths = PathEnumerator(f, b)
              if (paths.isEmpty) {
                val reaching = f.reachingTo(b)
                val looped = reaching.exists {
                  case br: Branch => br.isLoop
                  case _          => false
                }
                if (looped) loopBlocked += 1 else yetBlocked += 1
              } else {
                val goals =
                  try {
                    paths.flatMap(p => SymbolicInterpreter(f, p, cond)).toList
                  } catch { case _: NotImplementedError | _: MatchError => Nil }
                if (goals.isEmpty) missingTransfer += 1
                else if (
                  goals
                    .map(Solver.rewriteApps)
                    .forall(Reify.hasUninterpretableApp)
                ) appBlocked += 1
                else {
                  reifyFail += 1
                  val rewritten = goals.map(Solver.rewriteApps)
                  println(s"  [REIFY] ${f.name} Branch[${b.id}]")
                  for (g <- rewritten)
                    println(
                      s"          goal: ${g.mkString("\n                /\\ ")}",
                    )
                }
              }
        }
      }

      // timing summary
      if (timings.nonEmpty) {
        println(s"\n  Top 10 slowest:")
        for ((name, bid, ns) <- timings.sortBy(-_._3).take(10))
          println(f"    ${ns / 1_000_000.0}%8.2f ms  $name Branch[$bid]")
        val totalMs = timings.map(_._3).sum / 1_000_000.0
        val avgUs = timings.map(_._3).sum / timings.size / 1_000.0
        println(f"\n  Solve time: $totalMs%.1f ms total, $avgUs%.1f us avg")
      }

      // breakdown
      val total = loopBlocked + yetBlocked + missingTransfer +
        appBlocked + reifyFail + solved
      val addressable = total - loopBlocked - yetBlocked
      println(s"\n  Failure breakdown of $total direct branches:")
      println(s"    Solved:              $solved")
      println(s"    Loop-blocked:        $loopBlocked")
      println(s"    Yet-blocked:         $yetBlocked")
      println(s"    Missing transfer:    $missingTransfer")
      println(s"    App-blocked:         $appBlocked")
      println(s"    Reify/Solver fail:   $reifyFail")
      if (addressable > 0)
        println(
          f"\n  Addressable solve rate: $solved/$addressable" +
          f" (${solved * 100.0 / addressable}%.1f%%)",
        )
      if (total > 0)
        println(
          f"  Absolute solve rate:   $solved/$total" +
          f" (${solved * 100.0 / total}%.1f%%)",
        )

      // verification
      val verifyTotal = verified + verifyFailed
      println(s"\n  Verified: $verified / $verifyTotal solved")
      println(s"  Failed:   $verifyFailed")
      if (verifyTotal > 0)
        println(f"  Precision: ${verified * 100.0 / verifyTotal}%.1f%%")

      // diagnostic: print which expressions caused failures
      val fe = SymbolicInterpreter.failedExprs.toList.sortBy(-_._2)
      if (fe.nonEmpty) {
        println(s"\n  Missing transfer breakdown (${fe.map(_._2).sum} hits):")
        for ((key, cnt) <- fe)
          println(f"    $cnt%4d  $key")
      }

      assert(solved > 0)
      assert(verified > 0)
    }

    check("builtin branches: summary") {
      val dt = targetBranches(builtins).size
      val ct = targetBranches(helpers).size
      val total = dt + ct
      val exdt = targetBranches(allBuiltins).size - dt
      println(
        s"  Builtin functions:        ${builtins.size} (${allBuiltins.size - builtins.size} excluded)",
      )
      println(s"  Reachable helpers:         ${helpers.size}")
      println(s"  Direct target branches:    $dt ($exdt excluded)")
      println(s"  Callee target branches:    $ct")
      println(s"  Total target branches:     $total")
      if (total > 0)
        println(
          s"  Total coverage:            $verified/$total" +
          f" (${verified * 100.0 / total}%.1f%%)",
        )
      assert(total > 0)
    }
  }

  init
}
