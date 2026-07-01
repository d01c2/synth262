package synth262.state.util

import synth262.cfg.*
import synth262.cfg.util.{JsonProtocol => CFGJsonProtocol}
import synth262.spec.*
import synth262.util.*
import synth262.state.*
import io.circe.*, io.circe.syntax.*, io.circe.generic.semiauto.*

class JsonProtocol(cfg: CFG) extends CFGJsonProtocol(cfg) {
  // abstraction of call stacks as simple paths
  given callPathDecoder: Decoder[CallPath] =
    Decoder.instance(
      _.value.as[List[Call]].map(calls => CallPath(calls, calls.toSet)),
    )

  given callPathEncoder: Encoder[CallPath] =
    Encoder.instance(cp => Json.fromValues(cp.path.map(_.asJson)))

  // ECMAScript features
  given featureDecoder: Decoder[Feature] =
    Decoder.instance(c =>
      for {
        func <- funcDecoder(c)
        feature <- func.head match
          case Some(head: SyntaxDirectedOperationHead) =>
            Right(SyntacticFeature(func, head))
          case Some(head: BuiltinHead) =>
            Right(BuiltinFeature(func, head))
          case _ =>
            invalidFail("feature", c)
      } yield feature,
    )
  given featureEncoder: Encoder[Feature] =
    Encoder.instance(f => funcEncoder(f.func))
}
