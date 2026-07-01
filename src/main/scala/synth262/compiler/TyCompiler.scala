package synth262.compiler

import synth262.lang.Type
import synth262.ty.*
import synth262.ty.util.{Walker => TyWalker}

object TyCompiler extends TyWalker {
  override def walk(ty: UnknownTy): UnknownTy =
    UnknownTy(ty.msg.map(Type.normalizeName))
}
