package esmeta.llm

import esmeta.util.BasicJsonProtocol
import io.circe.*

object JsonProtocol extends BasicJsonProtocol {

  case class BatchResponseLine(
    customId: Option[String],
    statusCode: Option[Int],
    output: Vector[OutputItem],
  )

  case class OutputItem(
    kind: Option[String],
    content: Vector[ContentItem],
  )

  case class ContentItem(
    kind: Option[String],
    text: Option[String],
  )

  given Decoder[ContentItem] = Decoder.instance { c =>
    for {
      kind <- c.get[Option[String]]("type")
      text <- c.get[Option[String]]("text")
    } yield ContentItem(kind, text)
  }

  given Decoder[OutputItem] = Decoder.instance { c =>
    for {
      kind <- c.get[Option[String]]("type")
      content <- c.get[Option[Vector[ContentItem]]]("content")
    } yield OutputItem(kind, content.getOrElse(Vector.empty))
  }

  given Decoder[BatchResponseLine] = Decoder.instance { c =>
    if (!c.value.isObject) Left(DecodingFailure("expected object", c.history))
    else {
      val customId = c
        .get[String]("custom_id")
        .toOption
        .orElse(c.get[Int]("custom_id").toOption.map(_.toString))
      val statusCode = c.downField("response").get[Int]("status_code").toOption
      val output = c
        .downField("response")
        .downField("body")
        .get[Option[Vector[OutputItem]]]("output")
        .toOption
        .flatten
        .getOrElse(Vector.empty)
      Right(BatchResponseLine(customId, statusCode, output))
    }
  }
}
