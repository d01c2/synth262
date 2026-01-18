package esmeta.phase

import esmeta.*
import esmeta.cfg.CFG
import esmeta.es.util.*
import esmeta.llm.*
import esmeta.llm.JsonProtocol.{*, given}
import esmeta.test262.{*, given}
import esmeta.util.*
import esmeta.util.SystemUtils.*
import scala.util.{Try, Using}
import io.circe.*, io.circe.syntax.*, io.circe.parser.*
import scala.io.Source

/** `llm-evaluate` phase */
case object LLMEvaluate extends Phase[CFG, Yaml] {
  val name = "llm-evaluate"
  val help = "evaluates LLM to generate ECMAScript tests."

  def apply(cfg: CFG, cmdConfig: CommandConfig, config: Config): Yaml =
    import Coverage.*

    lazy val scriptParser = cfg.scriptParser

    TEST_MODE = true
    val version = Test262.getVersion(None)
    val test262 = Test262(version, cfg)
    val (cov, _): (Coverage, Summary) = test262.evalTest(
      useProgress = config.debug,
      useCoverage = true,
      concurrent = ConcurrentPolicy.Auto,
    )
    println("- Target conditions collected based on Test262Test")

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

    lazy val batchRunner = BatchRunner

    // build requests.jsonl based on prompts
    val requestPath = batchRunner.dumpBatchRequests(prompts)

    // request LLM with requests.jsonl
    val batchId = batchRunner.sendBatchRequests(requestPath)

    // poll for batch completion (blocking)
    val responsePath = batchRunner.getBatchResponse(batchId)

    val outputDir = s"$LLM_LOG_DIR/out"
    val (written, _) = extractBatchResponses(responsePath, outputDir)
    println(s"- Extracted $written JS files into $outputDir .")

    lazy val uncoveredCondMap: Map[Int, Cond] = (for {
      targetCond <- targetConds
      uncovered = targetCond.neg
    } yield (uncovered.id, uncovered)).toMap

    val results: Seq[Result] = (for {
      file <- walkTree(outputDir).toList
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
      name = "failed target branch ids (reached but failed)",
      data = failed_reached.map(_.cond.id).toList.asJson,
      filename = s"$LLM_LOG_DIR/failed_reached.json",
      noSpace = false,
    )
    dumpJson(
      name = "failed target branch ids (failed to reach)",
      data = failed_unreached.map(_.cond.id).toList.asJson,
      filename = s"$LLM_LOG_DIR/failed_unreached.json",
      noSpace = false,
    )
    dumpJson(
      name = "failed target branch ids (failed to parse)",
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

  private def extractOutputText(output: Vector[OutputItem]): String =
    val messageBlocks = output.filter(_.kind.contains("message"))
    val blocksToScan = if (messageBlocks.nonEmpty) messageBlocks else output

    val chunks = Vector.newBuilder[String]
    for (block <- blocksToScan) {
      for (content <- block.content) {
        if (content.kind.contains("output_text"))
          content.text.foreach(chunks += _)
      }
    }

    chunks.result().mkString("\n")

  private def extractBatchResponses(
    responsePath: String,
    logDir: String,
  ): (Int, Int) =
    mkdir(logDir)
    Using.resource(Source.fromFile(responsePath, "UTF-8")) { source =>
      source.getLines.zipWithIndex.foldLeft((0, 0)) {
        case ((written, skipped), (rawLine, _)) =>
          val trimmed = rawLine.trim
          if (trimmed.isEmpty) (written, skipped)
          else {
            parse(trimmed) match
              case Left(_) => (written, skipped + 1)
              case Right(json) =>
                json.as[BatchResponseLine] match
                  case Left(_) => (written, skipped + 1)
                  case Right(batchLine) =>
                    (batchLine.statusCode, batchLine.customId) match
                      case (Some(200), Some(id)) =>
                        val text = extractOutputText(batchLine.output)
                        if (text.nonEmpty) {
                          dumpFile(text, s"$logDir/$id.js");
                          (written + 1, skipped)
                        } else (written, skipped + 1)
                      case _ => (written, skipped + 1)
          }
      }
    }

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
