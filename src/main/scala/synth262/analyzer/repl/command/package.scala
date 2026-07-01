package synth262.analyzer.repl.command

import synth262.analyzer.{Analyzer, repl}

type Self = Decl & repl.Decl & Analyzer

trait Decl
  extends CommandDecl
  with CmdBreakDecl
  with CmdContinueDecl
  with CmdEntryDecl
  with CmdExitDecl
  with CmdFindImprecDecl
  with CmdGraphDecl
  with CmdHelpDecl
  with CmdInfoDecl
  with CmdJumpDecl
  with CmdListBreakDecl
  with CmdLogDecl
  with CmdMoveDecl
  with CmdPrintDecl
  with CmdRmBreakDecl
  with CmdStopDecl
  with CmdWorklistDecl {
  self: Self =>
}
