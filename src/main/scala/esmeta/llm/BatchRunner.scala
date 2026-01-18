package esmeta.llm

import esmeta.*
import esmeta.error.NoEnvVarError
import esmeta.util.SystemUtils.*
import io.circe.*
import io.circe.syntax.*
import io.circe.parser.*
import scala.sys.process.*
import scala.util.Try
import esmeta.util.BaseUtils.raise

/** Batch runner for OpenAI Batch API */
object BatchRunner {

  private def apiKey = sys.env.getOrElse("OPENAI_API_KEY", throw NoEnvVarError)

  def dumpBatchRequests(prompts: Seq[Prompt]): Unit =
    val batchRequests = prompts
      .map { prompt =>
        val body = Json.obj(
          "model" -> "gpt-5-mini".asJson,
          "input" -> prompt.text.asJson,
          "reasoning" -> Json.obj(
            "effort" -> "minimal".asJson,
            "summary" -> Json.Null,
          ),
          "text" -> Json.obj("verbosity" -> "low".asJson),
        )
        val batchRequest = Json.obj(
          "custom_id" -> prompt.cond.id.toString.asJson,
          "method" -> "POST".asJson,
          "url" -> "/v1/responses".asJson,
          "body" -> body,
        )
        batchRequest.noSpaces
      }
      .mkString("\n")
    val logDir = s"$LLM_LOG_DIR/requests.jsonl"
    dumpFile(batchRequests, logDir)
    println(s"- Dumped LLM batch requests into $logDir.")

  // def uploadBatchInputFileCurl: String =
  //   val cmd: Seq[String] = Seq(
  //     Seq("curl", "-sS", "https://api.openai.com/v1/files"),
  //     Seq("-H", s"Authorization: Bearer $apiKey"),
  //     Seq("-F", "purpose=batch"),
  //     Seq("-F", s"file=@$DUMP_LLM_PROMPTS_LOG_DIR/requests.jsonl"),
  //   ).flatten

  //   val err = new StringBuilder
  //   val out = Try(Process(cmd).!!).getOrElse(raise("Batch upload failed"))

  //   parse(out)
  //     .flatMap(_.hcursor.get[String]("id")) // input File object's ID
  //     .getOrElse(raise(s"Batch upload failed: Bad JSON"))

}
