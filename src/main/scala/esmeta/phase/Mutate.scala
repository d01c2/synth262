package esmeta.phase

import esmeta.*
import esmeta.analyzer.paramflow.*
import esmeta.cfg.CFG
import esmeta.es.*
import esmeta.es.util.*
import esmeta.fuzzer.mutator.*
import esmeta.util.*
import esmeta.util.SystemUtils.*
import esmeta.util.BaseUtils.*
import java.util.concurrent.TimeoutException
import scala.Console.*

/** `mutate` phase */
case object Mutate extends Phase[CFG, String] {
  val name = "mutate"
  val help = "mutates an ECMAScript program."
  def apply(cfg: CFG, cmdConfig: CommandConfig, config: Config): String =
    import Coverage.*

    val filename = getFirstFilename(cmdConfig, this.name)
    val code = readFile(filename)

    val analyzer: Option[ParamFlowAnalyzer] =
      if (config.analyze) {
        val an = ParamFlowAnalyzer(cfg, silent = true)
        an.analyze
        Some(an)
      } else None
    val cov = Coverage(
      cfg,
      kFs = config.kFs,
      timeLimit = Some(1),
      analyzer = analyzer,
    )

    // detect which side of the target branch is covered by the given program
    val coveredCondView: Option[CondView] = config.targetBranchId.map { id =>
      val interp = cov.run(code)
      // update targetCondViews on the coverage object
      cov.check(Script(code, "seed", true), interp)
      interp.touchedCondViews.keySet
        .filter(_.cond.branch.id == id)
        .headOption
        .getOrElse(raise(s"branch $id is not covered by the given program"))
    }

    val targetCondView = coveredCondView.map(_.neg)

    // print localization info
    for (cv <- coveredCondView) {
      val funcName = cfg.funcOf.get(cv.cond.branch).map(_.name).getOrElse("?")
      val targets = cov.targetCondViews
        .getOrElse(cv.cond, Map())
        .getOrElse(cv.view, Set())
      println(s"[mutate] covered: ${cv.cond.simpleString} (@ $funcName)")
      println(s"[mutate] target: ${cv.neg.cond.simpleString} (@ $funcName)")
      println(s"[mutate] program: ${setColor(CYAN)(code.trim())}")
      if (targets.isEmpty) println(s"[mutate] no targets found for this branch")
      else
        targets.foreach { t =>
          val snippet = setColor(CYAN)(t.loc.getString(code))
          val astInfo = setColor(YELLOW)(s"$t ${t.loc}")
          println(s"[mutate] localized to $astInfo: $snippet")
        }
    }

    given CFG = cfg
    val mutator: Mutator = TargetMutator()
    var blocked = Set[String]()
    var iter = 0

    val startTime = System.currentTimeMillis
    def elapsed = System.currentTimeMillis - startTime
    def timeout = config.duration.fold(false)(_ * 1000 < elapsed)
    def checkTimeout(): Unit = if (timeout) throw TimeoutException("mutate")

    def nextMutant(): String =
      val m = mutator(code, coveredCondView.map((_, cov))).code
      iter += 1
      m

    def coversTarget(code: String): Boolean = targetCondView.exists { cv =>
      try {
        val covered = cov.run(code).touchedCondViews.keySet.contains(cv)
        if (covered) println(s"[mutate] Covered in $iter iterations")
        covered
      } catch { case _: Exception => false }
    }

    var mutatedCode = nextMutant()

    // repeat until the mutated program is valid and covers target
    if (coveredCondView.isDefined)
      try {
        while (!(ValidityChecker(mutatedCode) && coversTarget(mutatedCode))) {
          checkTimeout()
          mutatedCode = nextMutant()
          while (blocked.contains(mutatedCode))
            checkTimeout()
            mutatedCode = nextMutant()
          blocked += mutatedCode
        }
      } catch {
        case _: TimeoutException =>
          println(s"[mutate] Timeout after $iter iterations")
          mutatedCode = setColor(RED)("FAILED TO MUTATE WITHIN TIMELIMIT")
      }

    // dump the mutated ECMAScript program
    for (filename <- config.out)
      dumpFile(
        name = "the mutated ECMAScript program",
        data = mutatedCode,
        filename = filename,
      )

    mutatedCode

  def defaultConfig: Config = Config()
  val options: List[PhaseOption[Config]] = List(
    (
      "out",
      StrOption((c, s) => c.out = Some(s)),
      "dump the mutated ECMAScript program to a given path.",
    ),
    (
      "branch",
      NumOption((c, k) => c.targetBranchId = Some(k)),
      "target branch id to cover the uncovered side.",
    ),
    (
      "kfs",
      NumOption((c, k) => c.kFs = k),
      "feature sensitivity level for targeting (default: 0).",
    ),
    (
      "analyze",
      BoolOption((c, b) => c.analyze = b),
      "use dataflow analysis for target guidance (default: true).",
    ),
    (
      "duration",
      NumOption((c, k) => c.duration = Some(k)),
      "set the maximum duration for mutation in seconds (default: INF).",
    ),
  )
  class Config(
    var out: Option[String] = None,
    var targetBranchId: Option[Int] = None,
    var kFs: Int = 0,
    var analyze: Boolean = true,
    var duration: Option[Int] = None,
  )
}
