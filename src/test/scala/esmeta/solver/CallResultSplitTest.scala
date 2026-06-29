package esmeta.solver

import esmeta.*
import esmeta.cfg.*
import esmeta.ir.*
import esmeta.ir.util.UnitWalker
import esmeta.ty.*
import esmeta.util.BaseUtils.*
import esmeta.util.SystemUtils.*
import scala.collection.mutable.{Map => MMap, Queue, Set => MSet}

/** Counts how call results are split by downstream branches */
class CallResultSplitTest extends SolverTest {

  /** test name */
  val name: String = "callResultSplitTest"

  lazy val cfg = ESMetaTest.cfg

  // ---------------------------------------------------------------------------
  // private helpers
  // ---------------------------------------------------------------------------
  // local variables inside an IR element
  private def locals(elem: IRElem): Set[Local] =
    val acc = MSet[Local]()
    val walker = new UnitWalker {
      override def walk(x: Var): Unit = x match
        case l: Local => acc += l
        case _        => ()
    }
    walker.walk(elem)
    acc.toSet

  private val Direct = "direct"
  private val ValueField = "value"
  private val CompletionKind = "completion-kind"

  private def completionTypes(name: String): Set[ValueTy] = name match
    case "normal"   => Set(NormalT, AbruptT)
    case "break"    => Set(BreakT)
    case "continue" => Set(ContinueT)
    case "return"   => Set(ReturnT)
    case "throw"    => Set(ThrowT)
    case _          => Set(EnumT(name))

  private def literalValueTypes(expr: Expr): Set[ValueTy] = expr match
    case EUndef()     => Set(UndefT)
    case ENull()      => Set(NullT)
    case EBool(value) => Set(BoolT(value))
    case EEnum(name)  => Set(EnumT(name))
    case _            => Set()

  private def typeOfTypes(expr: Expr): Set[ValueTy] = expr match
    case EStr(name) =>
      val ty = ValueTy.fromTypeOf(name)
      if (ty.isBottom) Set() else Set(ty)
    case _ => Set()

  private def refUse(
    ref: Ref,
    flow: Map[Local, Set[String]],
  ): Set[String] = ref match
    case local: Local =>
      flow.getOrElse(local, Set())
    case Field(base, EStr(field)) =>
      val baseUse = refUse(base, flow)
      if (!baseUse(Direct)) Set()
      else
        field match
          case "Value" => Set(ValueField)
          case "Type"  => Set(CompletionKind)
          case _       => Set()
    case _ => Set()

  private def exprUse(
    expr: Expr,
    flow: Map[Local, Set[String]],
  ): Set[String] = expr match
    case ERef(ref)               => refUse(ref, flow)
    case EUnary(_, operand)      => exprUse(operand, flow)
    case EBinary(_, left, right) => exprUse(left, flow) ++ exprUse(right, flow)
    case ETypeOf(base)           => exprUse(base, flow)
    case ETypeCheck(base, _)     => exprUse(base, flow)
    case EInstanceOf(base, _)    => exprUse(base, flow)
    case _                       => Set()

  private def refinedDemand(
    base: Expr,
    ty: ValueTy,
    flow: Map[Local, Set[String]],
  ): Set[ValueTy] =
    val use = exprUse(base, flow)
    Set.from(
      List(
        Option.when(use(Direct))(ty),
        Option.when(use(ValueField))(NormalT(ty)),
      ).flatten,
    )

  private def completionSplitTypes(ty: ValueTy): Set[ValueTy] =
    if (ty <= AbruptT) Set(ty, NormalT)
    else if (ty <= NormalT) Set(ty, AbruptT)
    else Set(ty)

  private def typeCheckDemand(
    base: Expr,
    ty: ValueTy,
    flow: Map[Local, Set[String]],
  ): Set[ValueTy] =
    val use = exprUse(base, flow)
    Set.from(
      List(
        Option.when(use(Direct))(completionSplitTypes(ty)),
        Option.when(use(ValueField))(Set(NormalT(ty))),
      ).flatten.flatten,
    )

  private def literalDemand(
    base: Expr,
    literal: Expr,
    flow: Map[Local, Set[String]],
  ): Set[ValueTy] =
    literalValueTypes(literal)
      .map(refinedDemand(base, _, flow))
      .foldLeft(Set[ValueTy]())(_ ++ _)

  private def completionKindDemand(
    left: Expr,
    right: Expr,
    flow: Map[Local, Set[String]],
  ): Set[ValueTy] =
    def isCompletionKind(expr: Expr): Boolean =
      exprUse(expr, flow)(CompletionKind)
    (left, right) match
      case (l, EEnum(name)) if isCompletionKind(l) => completionTypes(name)
      case (EEnum(name), r) if isCompletionKind(r) => completionTypes(name)
      case _                                       => Set()

  private def boolDemand(
    left: Expr,
    right: Expr,
    flow: Map[Local, Set[String]],
  ): Set[ValueTy] =
    def labels(base: Expr, value: Boolean): Set[ValueTy] =
      val use = exprUse(base, flow)
      Set.from(
        List(
          Option.when(use(Direct))(BoolT(value)),
          Option.when(use(Direct))(BoolT(!value)),
          Option.when(use(ValueField))(NormalT(BoolT(value))),
          Option.when(use(ValueField))(NormalT(BoolT(!value))),
        ).flatten,
      )
    (left, right) match
      case (l, EBool(value)) => labels(l, value)
      case (EBool(value), r) => labels(r, value)
      case _                 => Set()

  private def typeOfDemand(
    left: Expr,
    right: Expr,
    flow: Map[Local, Set[String]],
  ): Set[ValueTy] =
    (left, right) match
      case (ETypeOf(base), r) if exprUse(base, flow)(Direct) => typeOfTypes(r)
      case (l, ETypeOf(base)) if exprUse(base, flow)(Direct) => typeOfTypes(l)
      case _                                                 => Set()

  private def demandOn(
    expr: Expr,
    flow: Map[Local, Set[String]],
  ): Set[ValueTy] = expr match
    case ETypeCheck(base, ty) => typeCheckDemand(base, ty.toValue, flow)
    case ERef(ref) =>
      val use = refUse(ref, flow)
      Set.from(
        List(
          Option.when(use(Direct))(Set(TrueT, FalseT)),
          Option.when(use(ValueField))(Set(NormalT(TrueT), NormalT(FalseT))),
        ).flatten.flatten,
      )
    case EUnary(UOp.Not, operand) => demandOn(operand, flow)
    case EBinary(BOp.Eq, left, right) =>
      val completion = completionKindDemand(left, right, flow)
      val bools = boolDemand(left, right, flow)
      val literals =
        if (completion.nonEmpty || bools.nonEmpty) Set()
        else
          literalDemand(left, right, flow) ++ literalDemand(right, left, flow)
      completion ++ bools ++ typeOfDemand(left, right, flow) ++ literals
    case EBinary(BOp.And | BOp.Or, left, right) =>
      demandOn(left, flow) ++ demandOn(right, flow)
    case _ => Set()

  private def callRefLocals(call: Call): Set[Local] = call.callInst match
    case ICall(_, fexpr, args)      => (fexpr :: args).flatMap(locals).toSet
    case ISdoCall(_, base, _, args) => (base :: args).flatMap(locals).toSet

  private def updateFlow(
    lhs: Local,
    expr: Expr,
    flow: Map[Local, Set[String]],
  ): Map[Local, Set[String]] =
    val use = exprUse(expr, flow)
    if (use.isEmpty) flow - lhs else flow.updated(lhs, use)

  private def stepFlow(
    inst: NormalInst,
    flow: Map[Local, Set[String]],
  ): Map[Local, Set[String]] = inst match
    case ILet(lhs: Local, expr)    => updateFlow(lhs, expr, flow)
    case IAssign(lhs: Local, expr) => updateFlow(lhs, expr, flow)
    case _                         => flow

  private def stateKey(
    node: Node,
    flow: Map[Local, Set[String]],
  ): (Node, List[(Local, List[String])]) =
    (
      node,
      flow.toList.sortBy(_._1.toString).map {
        case (local, labels) => local -> labels.toList.sorted
      },
    )

  private def traceCall(
    call: Call,
  ): (List[Set[ValueTy]], Boolean) =
    val queue = Queue.empty[(Node, Map[Local, Set[String]])]
    var seen = Set.empty[(Node, List[(Local, List[String])])]
    var branchDemands = List.empty[Set[ValueTy]]
    var propagated = false

    def enqueue(next: Option[Node], flow: Map[Local, Set[String]]): Unit =
      next.foreach(node => queue.enqueue(node -> flow))

    enqueue(call.next, Map(call.lhs -> Set(Direct)))
    while (queue.nonEmpty) {
      val (node, flow) = queue.dequeue()
      val key = stateKey(node, flow)
      if (!seen(key)) {
        seen += key
        node match
          case block: Block =>
            var cur = flow
            var returned = false
            for (inst <- block.insts if !returned) {
              inst match
                case IReturn(expr) =>
                  if (exprUse(expr, cur).nonEmpty) propagated = true
                  returned = true
                case _ =>
                  cur = stepFlow(inst, cur)
            }
            if (!returned) enqueue(block.next, cur)

          case downstream: Call =>
            val isTracked = callRefLocals(downstream).exists { local =>
              flow.contains(local)
            }
            if (downstream.id != call.id && isTracked) propagated = true
            enqueue(downstream.next, flow)

          case branch: Branch =>
            val demand = demandOn(branch.cond, flow)
            if (exprUse(branch.cond, flow).nonEmpty) {
              val completed =
                if (branch.isAbruptNode && demand.isEmpty) Set(AbruptT)
                else demand
              branchDemands ::= completed
            }
            enqueue(branch.thenNode, flow)
            enqueue(branch.elseNode, flow)
      }
    }
    branchDemands.reverse -> propagated

  // ---------------------------------------------------------------------------
  // tests
  // ---------------------------------------------------------------------------
  def init: Unit = check("call-result splits at call sites") {
    var total = 0
    var demanded = 0
    var branched = 0
    var unknownBranch = 0
    var propagated = 0
    var other = 0
    val splitCounts = MMap[List[String], Int]()

    for {
      func <- cfg.funcs
      calls = func.nodes.collect { case call: Call => call }.toList
      call <- calls
    } {
      total += 1
      val (branchDemands, isPropagated) = traceCall(call)
      val demand = branchDemands.flatten.toSet
      if (demand.nonEmpty) {
        demanded += 1
        val split = demand.toList.map(_.toString).sorted
        splitCounts += split -> (splitCounts.getOrElse(split, 0) + 1)
      }
      if (branchDemands.nonEmpty) branched += 1

      if (demand.isEmpty)
        if (branchDemands.nonEmpty) unknownBranch += 1
        else if (isPropagated) propagated += 1
        else other += 1
    }

    val dir = s"$SOLVER_LOG_DIR/call-result-split"
    mkdir(dir, remove = true)

    val noBranch = total - branched
    val splitEntries = splitCounts.toList
      .sortBy { case (split, count) => (-count, split.mkString(" | ")) }
    val splitRows = splitEntries
      .map {
        case (split, count) =>
          Vector(
            "demand-split",
            split.mkString(" | "),
            count,
            "extracted-demand",
            demanded,
            percentString(count, demanded),
            total,
            percentString(count, total),
          )
      }
    val summaryRows = List(
      Vector(
        "class",
        "split",
        "sites",
        "parent-class",
        "parent-sites",
        "parent-percent",
        "total-sites",
        "total-percent",
      ),
      Vector(
        "result-branch",
        "(any)",
        branched,
        "all-call-sites",
        total,
        percentString(branched, total),
        total,
        percentString(branched, total),
      ),
      Vector(
        "extracted-demand",
        "(any)",
        demanded,
        "result-branch",
        branched,
        percentString(demanded, branched),
        total,
        percentString(demanded, total),
      ),
    ) ++ splitRows ++ List(
      Vector(
        "unknown-branch",
        "(none)",
        unknownBranch,
        "result-branch",
        branched,
        percentString(unknownBranch, branched),
        total,
        percentString(unknownBranch, total),
      ),
      Vector(
        "no-result-branch",
        "(none)",
        noBranch,
        "all-call-sites",
        total,
        percentString(noBranch, total),
        total,
        percentString(noBranch, total),
      ),
      Vector(
        "propagated-only",
        "(none)",
        propagated,
        "no-result-branch",
        noBranch,
        percentString(propagated, noBranch),
        total,
        percentString(propagated, total),
      ),
      Vector(
        "other",
        "(none)",
        other,
        "no-result-branch",
        noBranch,
        percentString(other, noBranch),
        total,
        percentString(other, total),
      ),
    )

    dumpFile(
      summaryRows.map(_.mkString("\t")).mkString(LINE_SEP),
      s"$dir/summary.tsv",
    )

    val topSplits = splitEntries.take(10).map {
      case (split, count) =>
        f"      ${count}%6d/$demanded%-6d " +
        f"${percentString(count, demanded)}%-9s " +
        f"${percentString(count, total)}%-9s ${split.mkString(" | ")}"
    }
    val remaining = splitEntries.drop(10).map(_._2).sum
    val remainingLine =
      Option.when(remaining > 0)(
        f"      ${remaining}%6d/$demanded%-6d " +
        f"${percentString(remaining, demanded)}%-9s " +
        f"${percentString(remaining, total)}%-9s (remaining splits)",
      )
    val splitText = (topSplits ++ remainingLine).mkString("\n")
    println(s"""
=== Call-result splits at call sites ===
  total call sites:         $total
  result-branch uses:       $branched/$total ${percentString(branched, total)}
    extracted-demand:       $demanded/$branched
    unknown-branch:         $unknownBranch/$branched
  no result branch:         $noBranch/$total ${percentString(noBranch, total)}
    propagated-only:        $propagated/$noBranch
    other:                  $other/$noBranch

  top demanded splits under extracted-demand:
      sites/demand parent%   total%    split
$splitText

  dumped to $dir/summary.tsv
""")
  }

  init
}
