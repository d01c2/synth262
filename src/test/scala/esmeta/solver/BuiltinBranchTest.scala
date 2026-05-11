package esmeta.solver

import esmeta.ESMetaTest
import esmeta.cfg.{Branch, CFG, Call, Func}
import esmeta.es.util.Coverage
import esmeta.es.util.Coverage.Cond
import esmeta.ir.{EBool, EClo, ICall}
import esmeta.phase.Solve
import scala.collection.mutable.{Map => MMap, Set => MSet, Queue}

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

    val allBuiltins = cfg.funcs.filter(_.isBuiltin).sortBy(_.name)
    // probe each builtin: call with no args, exclude if unsupported or throws
    val builtins = allBuiltins.filter { f =>
      Reify.funcAccessExpr(f).exists { js =>
        try { cov.run(js + ".call();").supported }
        catch { case _: Throwable => false }
      }
    }
    var verified = 0

    // collect unique (builtin, branch) pairs — each branch solved once
    val targets: List[(Func, Branch)] = {
      val seen = MSet[Int]()
      val buf = List.newBuilder[(Func, Branch)]
      for (f <- builtins) {
        val reachable = reachableFuncs(List(f))
        for (b <- targetBranches(reachable).sortBy(_.id))
          if (seen.add(b.id)) buf += (f -> b)
      }
      buf.result()
    }

    check("builtin branches: solve and verify") {
      var solved = 0
      var unsolved = 0
      var verifyFailed = 0
      var timings = List[(String, Int, Long)]()
      val reasons = MMap[String, Int]()
      var contradictionSamples = List[(String, Int, List[Formula])]()
      var reifyFailedSamples = List[(String, Int, List[Formula])]()

      for ((f, b) <- targets) {
        val t0 = System.nanoTime()
        val cond = Cond(b, true)

        val candidates =
          try { Solve.solve(f, b, cond) }
          catch { case _: NotImplementedError | _: MatchError => Nil }

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
                verifyFailed += 1
                println(
                  f"  [MISS] ${f.name} Branch[${b.id}]:T (${elapsed / 1000.0}%.0f us)",
                )
                println(
                  s"         js: ${candidates.head}",
                )
                // dump constraint pipeline for case study
                val params = Solve.paramIds(f)
                val goals = SymbolicInterpreter(f, cond)
                for ((goal, gi) <- goals.zipWithIndex) {
                  println(s"         --- goal[$gi] raw ---")
                  for (c <- goal) println(s"           $c")
                  val rewritten = Solver.rewrite(goal)
                  println(s"         --- goal[$gi] rewritten ---")
                  for (c <- rewritten) println(s"           $c")
                  Solver.simplify(rewritten) match
                    case None =>
                      println(s"         --- goal[$gi] CONTRADICTION ---")
                    case Some(simplified) =>
                      println(s"         --- goal[$gi] simplified ---")
                      for (c <- simplified) println(s"           $c")
                      val w = Reify(simplified, params).witness
                      println(s"         --- goal[$gi] witness: $w ---")
                      w.foreach { wit =>
                        val js = Reify.toJsCall(f, params, wit)
                        println(s"         --- goal[$gi] toJsCall: $js ---")
                      }
                }
          case None =>
            unsolved += 1
            val reason =
              try {
                val goals = SymbolicInterpreter(f, cond)
                if (goals.isEmpty) "no-goals"
                else {
                  val params = Solve.paramIds(f)
                  goals
                    .map { goal =>
                      val rewritten = Solver.rewrite(goal)
                      Solver.simplify(rewritten) match
                        case None =>
                          if (contradictionSamples.size < 5)
                            contradictionSamples :+= (f.name, b.id, rewritten)
                          "contradiction"
                        case Some(fs) =>
                          if (Reify.hasUninterpretableApp(fs)) {
                            val names = fs.flatMap(Reify.outerAppNames).toSet
                            s"uninterp-app(${names.mkString(",")})"
                          } else
                            Reify(fs, params).witness match
                              case None =>
                                if (reifyFailedSamples.size < 5)
                                  reifyFailedSamples :+= (f.name, b.id, fs)
                                "reify-failed"
                              case Some(w) =>
                                Reify.toJsCall(f, params, w) match
                                  case None    => "no-js-call"
                                  case Some(_) => "unknown"
                    }
                    .groupBy(identity)
                    .maxBy(_._2.size)
                    ._1
                }
              } catch {
                case e: NotImplementedError =>
                  val site = e.getStackTrace.headOption
                    .map(_.getMethodName)
                    .getOrElse("?")
                  s"unimpl($site)"
                case e: MatchError =>
                  val msg = e.getMessage.take(60)
                  s"missing-transfer($msg)"
                case e: Throwable =>
                  s"error(${e.getClass.getSimpleName})"
              }
            reasons(reason) = reasons.getOrElse(reason, 0) + 1
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
        val others = List.newBuilder[(String, Int)]
        for ((reason, count) <- reasons.toList.sortBy(-_._2))
          if (reason.startsWith("uninterp-app("))
            uninterpTotal += count
          else others += (reason -> count)
        if (uninterpTotal > 0)
          others += ("uninterp-app" -> uninterpTotal)
        for ((reason, count) <- others.result().sortBy(-_._2))
          println(f"    $count%4d  $reason")
      }

      if (contradictionSamples.nonEmpty) {
        println(f"\n  Contradiction samples:")
        for ((name, bid, fs) <- contradictionSamples)
          println(s"    $name Branch[$bid]:")
          for (f <- fs) println(s"      $f")
      }

      if (reifyFailedSamples.nonEmpty) {
        println(f"\n  Reify-failed samples:")
        for ((name, bid, fs) <- reifyFailedSamples)
          println(s"    $name Branch[$bid]:")
          for (f <- fs) println(s"      $f")
      }

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
    }
  }

  init
}
