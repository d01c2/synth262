package esmeta.phase

import esmeta.*
import esmeta.cfg.*
import esmeta.es.*
import esmeta.es.util.{Coverage, flattenStmt}
import esmeta.error.InterpreterError
import esmeta.interpreter.Interpreter
import esmeta.spec.Grammar
import esmeta.state.State
import esmeta.test262.{*, given}
import esmeta.util.*
import esmeta.util.BaseUtils.*
import esmeta.util.{ConcurrentPolicy => CP}
import esmeta.util.SystemUtils.*
import java.io.File
import java.util.concurrent.{ConcurrentHashMap, ConcurrentLinkedQueue}
import java.util.concurrent.atomic.AtomicInteger
import scala.jdk.CollectionConverters.*
import scala.util.Try

/** `test262-shrink` phase */
case object Test262Shrink extends Phase[CFG, Unit] {
  val name = "test262-shrink"
  val help = "shrink all Test262 tests covering target-cond nodes."

  def apply(
    cfg: CFG,
    cmdConfig: CommandConfig,
    config: Config,
  ): Unit =
    // set test mode
    TEST_MODE = true

    // output directory with timestamp
    val baseDir = config.out.getOrElse(TEST262SHRINK_LOG_DIR)
    mkdir(baseDir)
    val logDir = s"$baseDir/shrink-$dateStr"
    val symlink = s"$baseDir/recent"
    mkdir(logDir)
    createSymLink(symlink, logDir, overwrite = true)

    // get target version of Test262
    val version = Test262.getVersion(config.target)
    val test262 = Test262(version, cfg)

    // get tests and filter
    val tests = test262.getTests()
    val (targetTests, removed) = test262.testFilter(tests)
    // collect coverage and build target-cond to test mapping
    val cov = Coverage(cfg = cfg, timeLimit = config.timeLimit)
    val condToTests =
      new ConcurrentHashMap[Int, ConcurrentLinkedQueue[String]]()

    val coverageBar = test262.getProgressBar(
      name = "coverage",
      targetTests = targetTests,
      pw = getPrintWriter(s"$logDir/log"),
      removed = removed,
      useProgress = config.progress,
      useErrorHandler = true,
      concurrent = config.concurrent,
    )

    for (test <- coverageBar) {
      val filename = test.path
      val (ast, sourceText) = test262.loadTest(filename)
      val script = Script(Code.Normal(sourceText), filename, true)
      val interp =
        cov.run(sourceText, ast, Some(script.code), Some(filename))
      cov.synchronized { cov.check(script, interp) }
      val touchedBranchIds =
        interp.touchedCondViews.keysIterator.map(_.cond.id).toSet
      for (nid <- touchedBranchIds)
        condToTests
          .computeIfAbsent(nid, _ => new ConcurrentLinkedQueue[String]())
          .add(test.relName)
    }

    // extract target-cond ids from coverage
    val targetCondIds = cov.targetCondViews.keysIterator.map(_.id).toSet
    val testMap = targetTests.map(t => t.relName -> t).toMap
    val maxTests = config.maxTests
    val nodeToTests: Map[Int, List[Test]] =
      condToTests.asScala.collect {
        case (nid, ts) if targetCondIds.contains(nid) =>
          val tests = ts.asScala.toList.flatMap(testMap.get)
          nid.intValue -> tests.sortBy(t => File(t.path).length).take(maxTests)
      }.toMap
    val targetNodeIds = nodeToTests.keys.toList.sorted

    // shrink per target-cond node
    val dd = new DeltaDebugger(cfg, config.timeLimit)
    val shrunkCount = AtomicInteger(0)

    val ddBar = ProgressBar(
      msg = s"shrinking tests for ${targetNodeIds.size} target-cond nodes",
      iterable = targetNodeIds,
      errorHandler = (_, _, _) => (),
      verbose = config.progress,
      concurrent = config.concurrent,
    )

    for (nid <- ddBar) {
      mkdir(s"$logDir/$nid")
      for (test <- nodeToTests(nid)) {
        var stmts = flattenStmt(cfg.scriptParser.fromFile(test.path))
        if (stmts.nonEmpty && dd.hitsNode(stmts, nid)) {
          stmts = dd.minimize(stmts, nid)
          val shrunkCode = dd.toSource(stmts)
          val outName = test.relName.replace("/", "_")
          dumpFile(shrunkCode, s"$logDir/$nid/$outName")
          shrunkCount.incrementAndGet()
        }
      }
    }

    println(s"- ${shrunkCount.get()} shrunk programs written to $logDir.")

  private class DeltaDebugger(cfg: CFG, timeLimit: Option[Int]) {
    private val grammar: Option[Grammar] = Some(cfg.grammar)

    /** serialize statements to valid JS source */
    def toSource(stmts: Vector[Ast]): String =
      stmts.map(_.toString(grammar = grammar).trim).mkString("\n") + "\n"

    /** check whether the given statements hit the target node */
    def hitsNode(stmts: Vector[Ast], nodeId: Int): Boolean = try {
      val st = cfg.init.from(toSource(stmts))
      new NodeHitChecker(st, nodeId, timeLimit).result
      false
    } catch {
      case NodeHitException    => true
      case _: InterpreterError => false
    }

    /** minimization: statement ddmin + AST descendant replacement */
    def minimize(stmts: Vector[Ast], nodeId: Int): Vector[Ast] =
      var current = ddmin(stmts, nodeId)
      var changed = true
      while (changed) {
        changed = false
        var i = 0
        while (i < current.size) {
          val replaced = descendants(current(i)).exists { desc =>
            val candidate = current.updated(i, desc)
            val valid =
              Try(cfg.scriptParser.from(toSource(candidate))).isSuccess
            if (valid && hitsNode(candidate, nodeId)) {
              current = candidate; true
            } else false
          }
          if (replaced) { current = ddmin(current, nodeId); changed = true }
          else i += 1
        }
      }
      current

    /** statement-level ddmin-style chunk removal */
    private def ddmin(stmts: Vector[Ast], nodeId: Int): Vector[Ast] =
      var current = stmts
      var gran = math.max(1, current.size / 2)
      while (gran >= 1) {
        var i = 0
        var removed = false
        while (i < current.size) {
          val n = math.min(gran, current.size - i)
          val candidate = current.patch(i, Nil, n)
          if (candidate.nonEmpty && hitsNode(candidate, nodeId)) {
            current = candidate; removed = true
          } else i += gran
        }
        if (!removed) gran /= 2
      }
      current

    /** collect all syntactic descendants of an AST node */
    private def descendants(ast: Ast): List[Ast] = ast match
      case syn: Syntactic =>
        val children = syn.children.flatten.collect { case s: Syntactic => s }
        children.toList ++ children.flatMap(descendants)
      case _ => Nil
  }

  /** exception thrown when the target node is hit during interpretation */
  private case object NodeHitException extends Exception

  /** interpreter that throws on hitting the target node */
  private class NodeHitChecker(
    initSt: State,
    targetNodeId: Int,
    timeLimitSec: Option[Int],
  ) extends Interpreter(initSt, timeLimit = timeLimitSec) {
    override def eval(node: Node): Unit =
      if (node.id == targetNodeId) throw NodeHitException
      super.eval(node)

    override def step: Boolean =
      try { super.step }
      catch {
        case NodeHitException    => throw NodeHitException
        case _: InterpreterError => false
      }
  }

  def defaultConfig: Config = Config()
  val options: List[PhaseOption[Config]] = List(
    (
      "target",
      StrOption((c, s) => c.target = Some(s)),
      "set the target git version of Test262 (default: current version).",
    ),
    (
      "out",
      StrOption((c, s) => c.out = Some(s)),
      "set the output directory (default: $TEST262SHRINK_LOG_DIR).",
    ),
    (
      "progress",
      BoolOption(_.progress = _),
      "show progress bar.",
    ),
    (
      "timeout",
      NumOption((c, k) => c.timeLimit = Some(k)),
      "set the time limit in seconds (default: no limit).",
    ),
    (
      "max-tests",
      NumOption((c, k) => c.maxTests = k),
      "max number of tests per target-cond node, shortest first (default: 10).",
    ),
    (
      "concurrent",
      NumOption((c, k) =>
        c.concurrent =
          if (k <= 0) then CP.Auto else if (k == 1) CP.Single else CP.Fixed(k),
      ),
      "set the number of thread to use concurrently (default: no concurrent)." +
      " If number <= 0, use automatically determined number of threads.",
    ),
  )
  case class Config(
    var target: Option[String] = None,
    var out: Option[String] = None,
    var progress: Boolean = false,
    var timeLimit: Option[Int] = None,
    var maxTests: Int = 10,
    var concurrent: CP = CP.Single,
  )
}
