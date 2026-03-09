package esmeta.es

import esmeta.cfg.CFG
import esmeta.util.Loc

/** Target Information */
case class Target(prodName: String, idx: Int, subIdx: Int, loc: Loc):
  override def toString: String = s"$prodName[$idx,$subIdx]"

object Target {

  /** create Target from AST */
  def apply(ast: Option[Ast])(using cfg: CFG): Option[Target] = for {
    case ast: Syntactic <- ast
    name = ast.name
    idx = ast.rhsIdx
    subIdx = ast.subIdx
    loc <- ast.loc
  } yield Target(name, idx, subIdx, loc)
}
