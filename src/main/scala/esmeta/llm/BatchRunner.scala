package esmeta.llm

import esmeta.*
import esmeta.error.NoEnvVarError
import esmeta.util.BaseUtils.*
import esmeta.util.SystemUtils.*
import io.circe.*
import io.circe.syntax.*
import io.circe.parser.*
import java.nio.file.*
import scala.jdk.OptionConverters.*
import scala.util.Using
import com.openai.client.OpenAIClient
import com.openai.client.okhttp.OpenAIOkHttpClient
import com.openai.models.files.*
import com.openai.models.batches.*

/** Batch runner for OpenAI Batch API */
object BatchRunner {

  private def apiKey = sys.env.getOrElse("OPENAI_API_KEY", throw NoEnvVarError)

  lazy val client = OpenAIOkHttpClient.builder().apiKey(apiKey).build()

  def dumpBatchRequests(prompts: Seq[Prompt]): String =
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

    val requestPath = s"$LLM_LOG_DIR/requests.jsonl"
    dumpFile(
      name = "LLM batch requests",
      data = batchRequests,
      filename = requestPath,
    )
    requestPath

  def sendBatchRequests(requestPath: String): String =
    val fileParams = FileCreateParams
      .builder()
      .purpose(FilePurpose.BATCH)
      .file(Paths.get(requestPath))
      .build()
    val fileObj = client.files().create(fileParams)

    val batchParams = BatchCreateParams
      .builder()
      .inputFileId(fileObj.id())
      .endpoint(BatchCreateParams.Endpoint.V1_RESPONSES)
      .completionWindow(BatchCreateParams.CompletionWindow._24H)
      .build()
    val batch = client.batches().create(batchParams)

    val batchId = batch.id()
    println(s"- Created batch: $batchId")
    batchId

  def getBatchResponse(
    batchId: String,
    pollInterval: Long = 5L * 60L * 1000L, // 5 min default
  ): String =
    def awaitCompletion(): Batch =
      val batch: Batch = client.batches().retrieve(batchId)
      val statusStr = batch.status().toString.toLowerCase
      if (statusStr.contains("completed")) batch
      else {
        val waitSec = pollInterval / 1000
        println(s"- Batch status: ${batch.status()}, polling again...")
        Thread.sleep(pollInterval)
        awaitCompletion()
      }

    val batch = awaitCompletion()

    val outputFileId = batch.outputFileId().toScala match
      case Some(id) => id
      case None     => raise(s"$batchId completed without output file id")

    val responsePath = s"$LLM_LOG_DIR/responses.jsonl"
    Using.resource(client.files().content(outputFileId)) { resp =>
      Files.copy(
        resp.body(),
        Paths.get(responsePath),
        StandardCopyOption.REPLACE_EXISTING,
      )
    }
    println(s"- Dumped LLM batch responses into $responsePath .")
    responsePath
}
