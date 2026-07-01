package synth262.cfg.util
import synth262.cfg.*
import synth262.util.*
import io.circe.*, io.circe.syntax.*, io.circe.generic.semiauto.*

class JsonProtocol(cfg: CFG) extends BasicJsonProtocol {
  // functions
  given funcDecoder: Decoder[Func] = uidDecoder(cfg.funcMap.get)
  given funcEncoder: Encoder[Func] = uidEncoder

  // nodes
  given nodeDecoder: Decoder[Node] = uidDecoder(cfg.nodeMap.get)
  given nodeEncoder: Encoder[Node] = uidEncoder

  // block nodes
  given blockDecoder: Decoder[Block] =
    uidDecoder(cfg.nodeMap.get(_).collect { case block: Block => block })
  given blockEncoder: Encoder[Block] = uidEncoder

  // call nodes
  given callDecoder: Decoder[Call] =
    uidDecoder(cfg.nodeMap.get(_).collect { case call: Call => call })
  given callEncoder: Encoder[Call] = uidEncoder

  // branch nodes
  given branchDecoder: Decoder[Branch] =
    uidDecoder(cfg.nodeMap.get(_).collect { case branch: Branch => branch })
  given branchEncoder: Encoder[Branch] = uidEncoder

}
