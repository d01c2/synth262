package esmeta.solver

import esmeta.ESMetaTest
import esmeta.cfg.{Branch, CFG, Func}
import esmeta.es.util.Coverage
import esmeta.es.util.Coverage.Cond
import esmeta.phase.Solve
import java.io.PrintWriter
import java.util.concurrent.{
  Callable,
  ExecutorCompletionService,
  Executors,
  ThreadFactory,
  TimeUnit,
  TimeoutException,
}
import scala.collection.mutable.{ArrayBuffer, Map => MMap}
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.concurrent.duration.Duration

/** Dumps pre-/post-solver constraints for branches that fuzzing covers but
  * the solver misses (`fuzz-result-0fs.txt` minus `solver-result.txt`,
  * tagged with BBT statuses parsed from `solve-dump.log`), so the failure
  * cause can be inspected per branch:
  *   - [pre-solver]: raw path constraint from the symbolic interpreter
  *   - [post-solver]: saturated solution before stripCallFacts
  *   - [dropped-by-stripCallFacts]: formulas the solver dropped
  *   - [final]: what the reifier sees
  *   - [contradicted-*]: goals rejected as contradictions (+ minimized core)
  *
  * Enabled only with FUZZ_GAP_DUMP=1 (analysis tool, not a regression test).
  * Output: fuzz-gap-dump.log
  */
class FuzzGapDump extends ESMetaTest {
  val name = "fuzzGapDump"
  val category = "solver"

  lazy val cfg = ESMetaTest.cfg

  private val fuzzResultPath = "fuzz-result-0fs.txt"
  private val solverResultPath = "solver-result.txt"
  private val bbtDumpPath = "solve-dump.log"
  private val dumpPath = "fuzz-gap-dump.log"
  private val enabled = sys.env.get("FUZZ_GAP_DUMP").contains("1")

  private def sideString(side: Boolean): String = if (side) "T" else "F"

  def init: Unit =
    if (!enabled)
      check("fuzz gap dump (set FUZZ_GAP_DUMP=1 to enable)") { () }
    else
      check("fuzz gap dump") { run() }

  private def run(): Unit = {
    given CFG = cfg
    // targets = (fuzz coverage) minus (solver coverage), each side tagged
    // with the BBT status parsed from solve-dump.log ("not-in-bbt" if the
    // side is outside the BBT target set)
    val sidePattern = """Branch\[(\d+)\]:([TF])""".r
    def readSides(path: String): Set[(Int, Boolean)] =
      scala.io.Source.fromFile(path).getLines().toSet.collect {
        case sidePattern(id, side) => (id.toInt, side == "T")
      }
    val statusPattern = """=== .* Branch\[(\d+)\]:([TF]) === (.*)""".r
    val bbtStatus: Map[(Int, Boolean), String] =
      scala.io.Source
        .fromFile(bbtDumpPath)
        .getLines()
        .collect {
          case statusPattern(id, side, st) => (id.toInt, side == "T") -> st
        }
        .toMap
    val gap = readSides(fuzzResultPath) -- readSides(solverResultPath)
    val wanted: List[(Int, Boolean, String)] =
      gap.toList.sorted.map((id, side) =>
        (id, side, bbtStatus.getOrElse((id, side), "not-in-bbt")),
      )
    println(
      s"  ${wanted.size} fuzz-not-solver branch sides " +
      s"($fuzzResultPath minus $solverResultPath)",
    )

    val branchById: Map[Int, Branch] =
      cfg.funcs
        .flatMap(_.nodes)
        .collect { case b: Branch => b.id -> b }
        .toMap

    val cov = Coverage(cfg, timeLimit = Some(10))
    val nThreads = Runtime.getRuntime.availableProcessors
    val pool = Executors.newFixedThreadPool(
      nThreads,
      new ThreadFactory {
        private var nextId = 0
        def newThread(r: Runnable): Thread = {
          nextId += 1
          val t = new Thread(r, s"fuzz-gap-dump-$nextId")
          t.setDaemon(true)
          t
        }
      },
    )
    given ExecutionContext = ExecutionContext.fromExecutor(pool)

    // accessible builtins (same filter as BuiltinBranchTest)
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
    val accessibleBuiltins = builtins.toSet
    val funcEntryCache = MMap[Int, List[Func]]()
    def entriesFor(b: Branch): List[Func] =
      funcEntryCache.getOrElseUpdate(
        cfg.funcOf(b).id,
        Solve.findEntries(b).filter(accessibleBuiltins.contains),
      )

    case class Target(entry: Func, cond: Cond, bbtStatus: String)
    case class TargetResult(
      bid: Int,
      side: Boolean,
      bbtStatus: String,
      nowStatus: String,
      droppedCount: Int,
      block: String,
    )

    val unresolved = ArrayBuffer[(Int, Boolean, String, String)]()
    val targets: List[Target] = wanted.flatMap { (bid, side, st) =>
      branchById.get(bid) match
        case None =>
          unresolved += ((bid, side, st, "unknown-branch-id")); None
        case Some(b) =>
          entriesFor(b) match
            case Nil =>
              unresolved += ((bid, side, st, "no-accessible-entry")); None
            case entry :: _ => Some(Target(entry, Cond(b, side), st))
    }
    println(
      s"  resolved: ${targets.size}, unresolved: ${unresolved.size}, " +
      s"threads: $nThreads",
    )

    def dumpTarget(t: Target): TargetResult = {
      val Target(entry, cond, bbtStatus) = t
      val b = cond.branch
      val targetFunc = cfg.funcOf(b)
      val solver = Solver(timeLimit = Some(90))
      Thread
        .currentThread()
        .setName(
          s"fuzz-gap-dump ${entry.name} " +
          s"Branch[${b.id}]:${sideString(cond.cond)}",
        )

      case class Trace(
        input: Option[List[Formula]],
        outs: ArrayBuffer[(List[Formula], List[Formula])],
        var forced: Int,
      )
      val traces = ArrayBuffer[Trace]()
      val maxStoredInputs = 50

      def tracedSolve(goal: List[Formula]): LazyList[List[Formula]] = {
        val input = if (traces.size < maxStoredInputs) Some(goal) else None
        val tr = Trace(input, ArrayBuffer(), 0)
        traces += tr
        solver.solveAllTraced(goal).map { (pre, post) =>
          tr.forced += 1
          if (tr.outs.size < 2) tr.outs += ((pre, post))
          post
        }
      }

      var status = "?"
      var js: Option[String] = None
      var reifiedGoal: Option[List[Formula]] = None
      var firstGoal: Option[List[Formula]] = None
      var interpOpt: Option[SymbolicInterpreter] = None
      try {
        val interp =
          SymbolicInterpreter(entry, cond, tracedSolve, solver.hasContradiction)
        interpOpt = Some(interp)
        try {
          val it = interp.result.take(20).iterator
          while (js.isEmpty && it.hasNext) {
            val fs = it.next()
            if (firstGoal.isEmpty) firstGoal = Some(fs)
            Reifier(entry, fs, Solve.paramIds(entry)).foreach { j =>
              js = Some(j); reifiedGoal = Some(fs)
            }
          }
        } catch {
          case _: NotImplementedError | _: MatchError => ()
        }
        status = (js, firstGoal) match
          case (Some(_), _) =>
            val dropped = Reifier
              .droppedAppNames(reifiedGoal.get, Solve.paramIds(entry))
            if (dropped.isEmpty) "solved(reified)"
            else s"solved(dropped-app:${dropped.toList.sorted.mkString(",")})"
          case (None, Some(fs)) =>
            val dropped = Reifier.droppedAppNames(fs, Solve.paramIds(entry))
            if (dropped.isEmpty) "reify-failed"
            else
              s"reify-failed(dropped-app:${dropped.toList.sorted.mkString(",")})"
          case (None, None) =>
            if (interp.targetContradiction) "contradiction"
            else if (interp.pathContradiction) "pruned"
            else if (interp.notImplBlocked.isDefined)
              s"no-goals(${interp.notImplBlocked.get})"
            else if (interp.loopBlocked) "no-goals(loop)"
            else if (interp.cycleBlocked) "no-goals(cycle)"
            else if (interp.stepInBlocked) "no-goals(step-in)"
            else if (interp.whitelistEmpty) "no-goals(whitelist-empty)"
            else if (interp.hasVariadic) "no-goals(variadic)"
            else if (interp.internalMethodDispatch)
              "no-goals(internal-method)"
            else "no-goals"
      } catch {
        case _: TimeoutException => status = "timeout"
        case e: NotImplementedError =>
          status = s"unimpl(${Option(e.getMessage).getOrElse("?")})"
        case e: MatchError =>
          status = s"missing-transfer(${e.getMessage.take(60)})"
        case e: Throwable =>
          status = s"error(${e.getClass.getSimpleName})"
      }

      // render the per-branch block
      val sb = new StringBuilder
      def line(s: String): Unit = { sb.append(s); sb.append('\n') }
      def fsLines(fs: List[Formula]): Unit =
        fs.foreach(f => line(s"    $f"))
      line(
        s"=== ${entry.name} -> ${targetFunc.name} " +
        s"Branch[${b.id}]:${sideString(cond.cond)} " +
        s"=== bbt:$bbtStatus | now:$status",
      )
      line(s"  [cfg] logs/cfg/func/${targetFunc.normalizedName}.cfg")
      js.foreach(j => line(s"  [js] $j"))
      val contradicted = traces.count(_.forced == 0)
      line(
        s"  [stats] solver-inputs=${traces.size} " +
        s"contradicted-inputs=$contradicted",
      )

      var droppedCount = 0
      traces.find(_.forced > 0).foreach { tr =>
        line("  [pre-solver] (raw path constraint from symbolic interpreter)")
        tr.input match
          case Some(in) => fsLines(in)
          case None     => line("    (not stored: beyond input cap)")
        tr.outs.headOption.foreach { (pre, post) =>
          line("  [post-solver] (saturated solution, before stripCallFacts)")
          fsLines(pre)
          val postSet = post.toSet
          val dropped = pre.filterNot(postSet)
          droppedCount = dropped.size
          line(s"  [dropped-by-stripCallFacts] (${dropped.size})")
          fsLines(dropped)
          line("  [final] (after strip; what the reifier sees)")
          fsLines(post)
        }
      }
      reifiedGoal.foreach { fs =>
        if (firstGoal.exists(_ != fs)) {
          line("  [reified-goal] (later goal used for the JS witness)")
          fsLines(fs)
        }
      }

      def dumpCore(in: List[Formula]): Unit =
        try {
          val minSolver = Solver(timeLimit = Some(15))
          if (minSolver.hasContradiction(in)) {
            var core = in
            if (in.sizeIs <= 50)
              for (f <- in if core.sizeIs > 1) {
                val cand = core.filterNot(_ == f)
                if (minSolver.hasContradiction(cand)) core = cand
              }
            line("  [contradiction-core] (minimized)")
            fsLines(core)
          } else
            line(
              "  [note] no direct contradiction; goal dies only after AO " +
              "case-split (every AoCase inconsistent)",
            )
        } catch {
          case _: TimeoutException =>
            line("  [note] contradiction-core minimization timed out")
        }

      val emptyTraces =
        traces.filter(tr => tr.forced == 0 && tr.input.isDefined).take(2)
      emptyTraces.zipWithIndex.foreach { (tr, i) =>
        line(
          s"  [contradicted-input #${i + 1}] (solver returned no solution)",
        )
        fsLines(tr.input.get)
        if (i == 0) dumpCore(tr.input.get)
      }
      interpOpt.foreach { interp =>
        interp.targetContradictionSamples.take(2).zipWithIndex.foreach {
          (g, i) =>
            line(
              s"  [contradicted-at-target-dnf #${i + 1}] " +
              "(pc ++ target-cond rejected before reaching the solver)",
            )
            fsLines(g)
            if (i == 0 && emptyTraces.isEmpty) dumpCore(g)
        }
      }
      if (status.startsWith("no-goals"))
        line(
          "  [note] symbolic interpreter produced no complete path " +
          "constraint; nothing reached the solver",
        )
      line("")

      TargetResult(
        b.id,
        cond.cond,
        bbtStatus,
        status,
        droppedCount,
        sb.toString,
      )
    }

    val completion = ExecutorCompletionService[TargetResult](pool)
    val targetIter = targets.iterator
    val resultBuilder = List.newBuilder[TargetResult]
    var submitted = 0
    var completed = 0

    def submitNext(): Unit =
      if (targetIter.hasNext) {
        val t = targetIter.next()
        completion.submit(new Callable[TargetResult] {
          def call(): TargetResult = dumpTarget(t)
        })
        submitted += 1
      }

    for (_ <- 0 until math.min(nThreads, targets.size)) submitNext()

    while (completed < targets.size) {
      val done = completion.poll(30, TimeUnit.SECONDS)
      if (done == null)
        println(
          s"  progress: $completed / ${targets.size} completed " +
          s"($submitted submitted)",
        )
      else {
        resultBuilder += done.get()
        completed += 1
        if (completed % 200 == 0)
          println(s"  progress: $completed / ${targets.size} completed")
        submitNext()
      }
    }
    val results =
      resultBuilder.result().sortBy(r => (r.bid, if (r.side) 0 else 1))

    val dumpFile = new PrintWriter(dumpPath)
    try {
      results.foreach(r => dumpFile.print(r.block))
      dumpFile.println("=" * 60)
      dumpFile.println(s"Unresolved targets (${unresolved.size})")
      for ((bid, side, st, why) <- unresolved)
        dumpFile.println(s"  Branch[$bid]:${sideString(side)}\tbbt:$st\t$why")
      dumpFile.println()
      dumpFile.println("=" * 60)
      dumpFile.println("Summary by current status")
      def collapseDropped(status: String): String =
        status.replaceAll("dropped-app:[^)]*", "dropped-app")
      val byStatus =
        results.groupMapReduce(r => collapseDropped(r.nowStatus))(_ => 1)(_ + _)
      for ((st, n) <- byStatus.toList.sortBy(-_._2))
        dumpFile.println(f"  $n%5d  $st")
      val solvedResults = results.filter(_.nowStatus.startsWith("solved("))
      val withDrop = solvedResults.count(_.droppedCount > 0)
      dumpFile.println()
      dumpFile.println(
        s"  solved(reified) with non-empty stripCallFacts drop: " +
        s"$withDrop / ${solvedResults.size}",
      )
    } finally dumpFile.close()

    println(s"  full dump written to $dumpPath")
    pool.shutdownNow()
    assert(results.nonEmpty)
  }

  init
}
