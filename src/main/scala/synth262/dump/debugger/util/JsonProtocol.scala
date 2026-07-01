package synth262.dump.debugger.util

import synth262.*
import synth262.cfg.CFG
import synth262.dump.debugger.DUMMY_BODY
import synth262.lang.*
import synth262.ir.*
import synth262.spec.*
import synth262.ty.*
import synth262.util.BasicJsonProtocol
import synth262.web.util.JsonProtocol as WebJsonProtocol
import io.circe.*, io.circe.syntax.*, io.circe.generic.semiauto.*

object JsonProtocol extends BasicJsonProtocol {

  import synth262.lang.util.JsonProtocol.given
  import synth262.ir.util.JsonProtocol.given
  import synth262.spec.util.JsonProtocol.given

  val algorithmOmittedDecoder: Decoder[Algorithm] = Decoder.instance { c =>
    for {
      head <- c.downField("head").as[Head]
      code <- c.downField("code").as[String]
    } yield Algorithm(head, DUMMY_BODY, code)
  }
  val algorithmOmittedEncoder: Encoder[Algorithm] = Encoder.instance { alg =>
    Json.obj(
      "head" -> alg.head.asJson,
      "code" -> alg.code.asJson,
    )
  }

  given Decoder[Func] = {
    given Decoder[Algorithm] = algorithmOmittedDecoder
    deriveDecoder[Func]
  }
  given Encoder[Func] = {
    given Encoder[Algorithm] = algorithmOmittedEncoder
    deriveEncoder[Func]
  }

  given Decoder[Spec.Version] = summon
  given Encoder[Spec.Version] = summon

  given Decoder[Table] = summon
  given Encoder[Table] = summon

  given Decoder[ty.TyModel] = summon
  given Encoder[ty.TyModel] = summon

  given Decoder[Grammar] = summon
  given Encoder[Grammar] = summon

  given Decoder[lang.Type] = summon
  given Encoder[lang.Type] = summon

}
