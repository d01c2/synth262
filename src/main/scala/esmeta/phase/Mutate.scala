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

/** `mutate` phase */
case object Mutate extends Phase[CFG, String] {
  val name = "mutate"
  val help = "mutates an ECMAScript program."
  def apply(cfg: CFG, cmdConfig: CommandConfig, config: Config): String =
    import Coverage.*, Target.*

    val jsonProtocol = new JsonProtocol(cfg)
    import jsonProtocol.{*, given}

    val grammar = cfg.grammar
    val filename = getFirstFilename(cmdConfig, this.name)
    val code =
      if (filename.endsWith(".js")) Code.Normal(readFile(filename))
      else if (filename.endsWith(".json")) readJson[Code](filename)
      else raise("invalid filename")

    val analyzer = ParamFlowAnalyzer(cfg, silent = true)
    analyzer.analyze
    val cov = Coverage(cfg, timeLimit = Some(1), analyzer = Some(analyzer))

    val coveredCondView: Option[CondView] =
      (config.targetBranchId, config.targetCond) match
        case (Some(id), Some(targetSide)) =>
          val touchedCondViews = cov.run(code).touchedCondViews.keySet
          val covered = touchedCondViews.filter { cv =>
            val CondView(Cond(branch, cond), _) = cv
            val coveredSide = !targetSide
            branch.id == id && cond == coveredSide
          }.headOption
          covered match
            case Some(covered) => Some(covered)
            case None => raise("not covering the flipped side of the target")
        case _ => None

    val targetCondView = coveredCondView.map(_.neg)

    val mutator = config.builder(using cfg)
    var blocked = Set[String]()
    var iter = 0

    val startTime = System.currentTimeMillis
    def elapsed = System.currentTimeMillis - startTime
    def timeout = config.duration.fold(false)(_ * 1000 < elapsed)

    // get a mutated code
    var mutatedCode = mutator(code, coveredCondView.map((_, cov))).code
    iter += 1

    // get string of mutated code
    def mutated = mutatedCode.toString

    def coversFlipped(code: Code): Boolean = targetCondView match
      case Some(cv) =>
        val covered = cov.run(code).touchedCondViews.keySet.contains(cv)
        if (covered) println(s"Covered $cv with $iter iters")
        covered
      case None => false

    // repeat until the mutated program is valid and covers target
    coveredCondView match
      case Some(cv) =>
        while (!(ValidityChecker(mutated) && coversFlipped(mutatedCode))) {
          while (blocked.contains(mutated))
            mutatedCode = mutator(code, coveredCondView.map((_, cov))).code
            iter += 1
          blocked += mutated
          if (timeout) throw TimeoutException("mutate")
        }
      case None => ()

    // dump the mutated ECMAScript program
    for (filename <- config.out)
      dumpFile(
        name = "the mutated ECMAScript program",
        data = mutated,
        filename = filename,
      )

    mutated

  def defaultConfig: Config = Config()
  val options: List[PhaseOption[Config]] = List(
    (
      "out",
      StrOption((c, s) => c.out = Some(s)),
      "dump the mutated ECMAScript program to a given path.",
    ),
    (
      "mutator",
      StrOption((c, s) =>
        c.builder = s match
          case "RandomMutator"     => RandomMutator()
          case "SpecStringMutator" => SpecStringMutator()
          case "TargetMutator"     => TargetMutator()
          case "StatementInserter" => StatementInserter()
          case "Remover"           => Remover()
          case _                   => RandomMutator(),
      ),
      "select a mutator (default: RandomMutator).",
    ),
    (
      "target-branch-id",
      NumOption((c, k) => c.targetBranchId = Some(k)),
      "repeat until the mutated program covers the targeted branch.",
    ),
    (
      "target-cond",
      StrOption((c, s) =>
        c.targetCond = s match
          case "true"  => Some(true)
          case "false" => Some(false)
          case _       => None,
      ),
      "repeat until the mutated program covers the targeted branch.",
    ),
    (
      "duration",
      NumOption((c, k) => c.duration = Some(k)),
      "set the maximum duration for mutation (default: INF).",
    ),
  )
  class Config(
    var out: Option[String] = None,
    var builder: CFG ?=> Mutator = RandomMutator(),
    var targetBranchId: Option[Int] = None,
    var targetCond: Option[Boolean] = None,
    // TODO: support feature sensitive targeting (for 1-FCPS)
    var duration: Option[Int] = None,
  )
}
