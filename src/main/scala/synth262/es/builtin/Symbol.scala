package synth262.es.builtin

import synth262.es.*
import synth262.cfg.CFG
import synth262.state.*
import synth262.ty.*

/** model for symbols */
case class Symbol(cfg: CFG) {
  private def spec = cfg.program.spec
  given CFG = cfg

  private lazy val symbols: List[String] = (for {
    row <- spec.tables(WELL_KNOWN_SYMBOLS).rows
    symbolField <- row.headOption.map(
      _.stripPrefix("%Symbol.").stripSuffix("%"),
    )
  } yield symbolField)

  /** get symbol record */
  def ty: ValueTy = RecordT("", symbols.map(x => x -> SymbolT(x)).toMap)

  /** get symbol record */
  def obj: RecordObj = recordObj("")(
    (for { symField <- symbols } yield symField -> symbolAddr(symField)): _*,
  )

  /** get map for heap */
  def map: Map[Addr, Obj] = (for { symField <- symbols } yield symbolAddr(
    symField,
  ) -> recordObj("Symbol")("Description" -> Str(symbolName(symField)))).toMap
}
