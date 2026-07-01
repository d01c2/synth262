package synth262.analyzer.repl

import synth262.analyzer.Analyzer

type Self = Decl & Analyzer

trait Decl extends ReplDecl with command.Decl { self: Self => }
