package synth262.error

import synth262.{VERSION, LINE_SEP}

class Synth262Error(
  val errMsg: String,
  val tag: String = s"Synth262 v$VERSION",
) extends Error(s"[$tag] $errMsg")

object NoEnvVarError
  extends Synth262Error(
    "Please set the environment variable SYNTH262_HOME." + LINE_SEP +
    "(See https://github.com/es-meta/esmeta#environment-setting)",
  )
