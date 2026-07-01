package synth262.phase

import synth262.*
import synth262.cfg.CFG
import synth262.error.{NotSupported => NSError, InterpreterError}
import synth262.injector.Injector
import synth262.interpreter.Interpreter
import synth262.es.*
import synth262.state.*
import synth262.test262.*
import synth262.util.*
import synth262.util.SystemUtils.*

/** `inject` phase */
case object Inject extends Phase[CFG, String] {
  val name = "inject"
  val help = "injects assertions to check final state of an ECMAScript file."

  private def injectFile(cfg: CFG, filename: String, config: Config): String =
    Injector.fromFile(cfg, filename, config.log).toString(detail = config.defs)

  private def injectFiles(
    cfg: CFG,
    dirname: String,
    config: Config,
  ): (List[(String, String)], Int) = {
    val files = listFiles(dirname)
      .filter(f => f.isFile && jsFilter(f.getName))
      .sortBy(_.getName)
    val injected = files.flatMap { file =>
      try Some(file.getName -> injectFile(cfg, file.getPath, config))
      catch { case _: InterpreterError | _: NSError => None }
    }
    (injected, files.size)
  }

  def apply(
    cfg: CFG,
    cmdConfig: CommandConfig,
    config: Config,
  ): String =
    val path = getFirstFilename(cmdConfig, this.name)
    if (config.batch) {
      val (injected, total) = injectFiles(cfg, path, config)
      config.out match
        case Some(dirname) =>
          mkdir(dirname, remove = true)
          for ((filename, source) <- injected)
            dumpFile(source, s"$dirname/$filename")
          s"Injected ${injected.size}/$total ECMAScript program(s), " +
          s"skipped ${total - injected.size}."
        case None =>
          injected.map(_._2).mkString(LINE_SEP + LINE_SEP)
    } else {
      val injected = injectFile(cfg, path, config)

      // dump the assertion-injected ECMAScript program
      for (filename <- config.out)
        dumpFile(
          name = "an assertion-injected ECMAScript program",
          data = injected,
          filename = filename,
        )

      injected
    }
  def defaultConfig: Config = Config()
  val options: List[PhaseOption[Config]] = List(
    (
      "defs",
      BoolOption(_.defs = _),
      "prepend definitions of helpers for assertions.",
    ),
    (
      "out",
      StrOption((c, s) => c.out = Some(s)),
      "dump assertion-injected ECMAScript program(s) to a given path.",
    ),
    (
      "log",
      BoolOption(_.log = _),
      "turn on logging mode.",
    ),
    (
      "batch",
      BoolOption(_.batch = _),
      "inject assertions into all JavaScript files in a target directory, " +
      "skipping not-supported files.",
    ),
  )
  case class Config(
    var defs: Boolean = false,
    var out: Option[String] = None,
    var log: Boolean = false,
    var batch: Boolean = false,
  )
}
