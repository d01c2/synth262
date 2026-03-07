package esmeta.es.util

import esmeta.*
import esmeta.es.*

/** merge statements to script */
def mergeStmt(l: Vector[Ast]): Ast =
  val params = List(false, false, false)
  val bodyOpt = l match
    case a +: rest =>
      val init: Ast = Syntactic("StatementList", params, 0, Vector(Some(a)))
        .setLoc(a.loc)
      val list = rest.foldLeft(init) {
        case (x, y) =>
          Syntactic("StatementList", Nil, 1, Vector(Some(x), Some(y)))
            .setLoc(x mergeLoc y)
      }
      Some(Syntactic("ScriptBody", Nil, 0, Vector(Some(list))))
    case _ => None
  Syntactic("Script", Nil, 0, Vector(bodyOpt))

/** flatten statement lists */
def flattenStmtList(
  s: Ast,
  stmts: Vector[Ast] = Vector.empty,
): Vector[Ast] = s match
  case Syntactic("StatementList", _, 0, Vector(Some(x0))) =>
    x0 +: stmts
  case Syntactic("StatementList", _, 1, Vector(Some(x0), Some(x1))) =>
    flattenStmtList(x0, x1 +: stmts)
  case _ => Vector.empty

/** flatten statements */
def flattenStmt(s: Ast): Vector[Ast] = s match
  case Syntactic("Script", _, 0, Vector(Some(body))) =>
    body match
      case Syntactic("ScriptBody", _, 0, Vector(Some(stmtList))) =>
        flattenStmtList(stmtList)
      case _ => Vector.empty
  case _ => Vector.empty

/** flatten argument lists */
def flattenArgList(ast: Ast): Vector[Ast] = ast match
  case Syntactic("ArgumentList", _, 0 | 1, children) =>
    children.flatten.toVector
  case Syntactic("ArgumentList", _, 2 | 3, children) =>
    children(0).map(flattenArgList).getOrElse(Vector()) ++
    children.lift(1).flatten.toVector
  case _ => Vector()

/** ECMAScript strict mode directive */
val USE_STRICT = s"\"use strict\";$LINE_SEP"
