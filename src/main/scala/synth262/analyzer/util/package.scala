package synth262.analyzer.util

import synth262.analyzer.Analyzer

type Self = Decl & Analyzer

trait Decl extends GraphDecl with DotPrinterDecl with StringifierDecl {
  self: Self =>
}
