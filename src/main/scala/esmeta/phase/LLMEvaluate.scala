package esmeta.phase

import esmeta.*
import esmeta.cfg.CFG
import esmeta.es.util.*
import esmeta.llm.*
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
    println("- target conditions collected based on Test262Test")

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

    // poll for batch completion every 5 minutes (blocking)
    val responsePath = batchRunner.getBatchResponse(batchId)

    val outputDir = s"$LLM_LOG_DIR/out"
    val (written, _) = extractBatchResponses(responsePath, outputDir)
    println(s"- extracted $written JS files into $outputDir .")

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

  private def extractOutputText(json: Json): String =
    val outputBlocks = json.hcursor
      .downField("response")
      .downField("body")
      .downField("output")
      .focus
      .flatMap(_.asArray)
      .getOrElse(Vector.empty)

    val messageBlocks = outputBlocks.filter { block =>
      block.hcursor.get[String]("type").toOption.contains("message")
    }

    val blocksToScan =
      if (messageBlocks.nonEmpty) messageBlocks
      else outputBlocks

    val chunks = Vector.newBuilder[String]
    for (block <- blocksToScan) {
      val contentItems = block.hcursor
        .downField("content")
        .focus
        .flatMap(_.asArray)
        .getOrElse(Vector.empty)
      for (content <- contentItems) {
        val cCursor = content.hcursor
        if (cCursor.get[String]("type").toOption.contains("output_text"))
          cCursor.get[String]("text").toOption.foreach(chunks += _)
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
        case ((written, skipped), (line, idx)) =>
          val lineNo = idx + 1
          val trimmed = line.trim
          if (trimmed.isEmpty) (written, skipped)
          else
            parse(trimmed) match
              case Left(_) => (written, skipped + 1)
              case Right(json) =>
                val cursor = json.hcursor
                val status = cursor
                  .downField("response")
                  .get[Int]("status_code")
                  .toOption
                val customId = cursor
                  .get[String]("custom_id")
                  .toOption
                  .orElse(
                    cursor.get[Int]("custom_id").toOption.map(_.toString),
                  )
                (status, customId) match
                  case (Some(200), Some(id)) =>
                    val text = extractOutputText(json)
                    if (text.nonEmpty)
                      dumpFile(text, s"$logDir/$id.js")
                      (written + 1, skipped)
                    else (written, skipped + 1)
                  case _ => (written, skipped + 1)
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
