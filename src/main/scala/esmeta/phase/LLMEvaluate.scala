package esmeta.phase

import esmeta.*
import esmeta.cfg.CFG
import esmeta.es.util.*
import esmeta.llm.*
import esmeta.test262.{*, given}
import esmeta.util.*
import esmeta.util.SystemUtils.*
import scala.util.Try
import io.circe.*, io.circe.syntax.*

/** `llm-evaluate` phase */
case object LLMEvaluate extends Phase[CFG, Yaml] {
  val name = "llm-evaluate"
  val help = "evaluates LLM to generate ECMAScript tests."

  def apply(cfg: CFG, cmdConfig: CommandConfig, config: Config): Yaml =
    import Coverage.*

    val jsonProtocol = new JsonProtocol(cfg)
    import jsonProtocol.{*, given}

    lazy val scriptParser = cfg.scriptParser

    TEST_MODE = true
    val version = Test262.getVersion(None)
    val test262 = Test262(version, cfg)
    val (cov, _): (Coverage, Summary) = test262.evalTest(
      useProgress = config.debug,
      useCoverage = true,
      concurrent = ConcurrentPolicy.Auto,
    )
    println("- Test262Test finished and loaded target conditions") // fixme

    lazy val targetConds = (for {
      targetCond <- cov.targetCondViews.keySet
      if !targetCond.branch.isFiltered
    } yield targetCond).toSeq.sorted

    lazy val promptBuilder = PromptBuilder(cfg, targetConds)
    lazy val prompts = promptBuilder.prompts

    dumpDir(
      name = "generated prompts",
      iterable = prompts,
      dirname = s"$LLM_LOG_DIR/prompts",
      getName = prompt => s"${prompt.cond.id}.prompt",
      getData = prompt => prompt.text,
      remove = true,
    )

    // TODO: request LLM with requests.jsonl
    // TODO: polling based batch completion checker (per 5 min?)
    // TODO: extraction from responses.jsonl to output js directory

    // FIXME: assume we have output js directory (local hard-coded)
    val path = "/Users/d01c2/Workspace/playground/batch-test/out"

    lazy val uncoveredCondMap: Map[Int, Cond] = (for {
      targetCond <- targetConds
      uncovered = targetCond.neg
    } yield (uncovered.id, uncovered)).toMap

    val results: Seq[Result] = (for {
      file <- walkTree(path).toList
      filepath = file.getPath
      filename = file.getName
      if jsFilter(filename)
    } yield {
      val id = filename.stripSuffix(".js").toInt
      val uncoveredCond = uncoveredCondMap(id)
      Try(scriptParser.fromFile(filepath)).toOption match
        case Some(ast) => {
          val cov = Coverage(cfg, timeLimit = Some(1))
          val touched: Set[Cond] =
            cov.run(ast).touchedCondViews.keySet.map(_.cond)
          val covered: Boolean = touched.exists(_ == uncoveredCond)
          val reached: Boolean = touched.exists(_ == uncoveredCond.neg)
          if (covered) Result(uncoveredCond, true, None)
          else {
            val msg = if (reached) "reached but failed" else "failed to reach"
            Result(uncoveredCond, false, Some(msg))
          }
        }
        case None => Result(uncoveredCond, false, Some("failed to parse"))
    }).sorted

    val passed = results.filter(result => result.status)
    val failed = results.filter(result => !result.status)
    val failed_reached = results.filter { result =>
      !result.status && result.reason == Some("reached but failed")
    }
    val failed_unreached = results.filter { result =>
      !result.status && result.reason == Some("failed to reach")
    }
    val failed_parse = results.filter { result =>
      !result.status && result.reason == Some("failed to parse")
    }

    dumpJson(
      name = "passed target branch ids",
      data = passed.map(_.cond.id).toList.asJson,
      filename = s"$LLM_LOG_DIR/passed.json",
      noSpace = false,
    )
    dumpJson(
      name = "reached but failed target branch ids",
      data = failed_reached.map(_.cond.id).toList.asJson,
      filename = s"$LLM_LOG_DIR/failed_reached.json",
      noSpace = false,
    )
    dumpJson(
      name = "failed to reach target branch ids",
      data = failed_unreached.map(_.cond.id).toList.asJson,
      filename = s"$LLM_LOG_DIR/failed_unreached.json",
      noSpace = false,
    )
    dumpJson(
      name = "failed to parse target branch ids",
      data = failed_parse.map(_.cond.id).toList.asJson,
      filename = s"$LLM_LOG_DIR/failed_parse.json",
      noSpace = false,
    )

    val summary = Yaml(
      Vector(
        "pass" -> passed.size,
        "fail" -> failed.size,
        "fail-details" -> Map(
          "reached but failed" -> failed_reached.size,
          "failed to reach" -> failed_unreached.size,
          "failed to parse" -> failed_parse.size,
        ),
      ) *,
    )

    dumpFile(
      name = "summary of LLM generated programs",
      data = summary,
      filename = s"$LLM_LOG_DIR/summary.yml",
    )

    summary

  def defaultConfig: Config = Config()
  val options: List[PhaseOption[Config]] = List(
    (
      "debug",
      BoolOption(_.debug = _),
      "turn on debug mode.",
    ),
  )
  case class Config(
    var debug: Boolean = false,
  )
}

case class Result(cond: Coverage.Cond, status: Boolean, reason: Option[String])
given Ordering[Result] = Ordering.by(_.cond.id)
