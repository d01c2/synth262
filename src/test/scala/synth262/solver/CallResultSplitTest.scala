package synth262.solver

import synth262.*
import synth262.analyzer.tychecker.TyChecker
import synth262.cfg.*
import synth262.ir.*
import synth262.ir.util.UnitWalker
import synth262.ty.*
import synth262.util.{Fin, Inf}
import synth262.util.BaseUtils.*
import synth262.util.SystemUtils.*
import scala.collection.mutable.{ListBuffer, Map => MMap, Queue, Set => MSet}

/** Counts how call results are split by downstream branches */
class CallResultSplitTest extends SolverTest {

  /** test name */
  val name: String = "callResultSplitTest"

  lazy val cfg = Synth262Test.cfg
  lazy val tychecker: TyChecker =
    val checker = TyChecker(cfg, silent = true)
    checker.analyze
    checker

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

  private def refUse(
    ref: Ref,
    flow: Map[Local, Set[String]],
  ): Set[String] = ref match
    case local: Local => flow.getOrElse(local, Set())
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
    case _ => locals(expr).flatMap(local => flow.getOrElse(local, Set()))

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

  private case class AnalyzedCallResult(resultTy: ValueTy, valueTy: ValueTy)

  private def sameTy(left: ValueTy, right: ValueTy): Boolean =
    left <= right && right <= left

  private def isStrictRefinement(before: ValueTy, after: ValueTy): Boolean =
    after <= before && !sameTy(before, after)

  private def abruptLabels(ty: ValueTy): Set[ValueTy] =
    if (!(ty && AbruptT).isBottom) Set(AbruptT) else Set()

  private def primitiveLabels(ty: ValueTy): Set[ValueTy] =
    val typeOfLabels =
      List(NumberT, BigIntT, StrT, ObjectT, SymbolT)
        .filter(label => !(ty && label).isBottom)
        .toSet
    Set.from(
      List(
        Option.when(!(ty && TrueT).isBottom)(TrueT),
        Option.when(!(ty && FalseT).isBottom)(FalseT),
        Option.when(ty.undef)(UndefT),
        Option.when(ty.nullv)(NullT),
      ).flatten,
    ) ++ (ty.enumv match
      case Fin(set) => set.map(EnumT(_))
      case Inf      => Set(EnumT)
    ) ++ typeOfLabels

  private def labelsFromUse(use: Set[String], ty: ValueTy): Set[ValueTy] =
    Set
      .from(
        List(
          Option.when(use(Direct))(ty),
          Option.when(use(ValueField))(NormalT(ty)),
        ).flatten,
      )
      .filterNot(_.isBottom)

  private def booleanSideLabels(
    expr: Expr,
    flow: Map[Local, Set[String]],
    side: ValueTy,
    exprTy: Expr => ValueTy,
  ): Set[ValueTy] =
    val sideValue =
      if (side <= TrueT) Some(true)
      else if (side <= FalseT) Some(false)
      else None
    sideValue match
      case None => Set()
      case Some(value) =>
        val ty = BoolT(value)
        expr match
          case ERef(ref) =>
            labelsFromUse(refUse(ref, flow), ty)
          case EUnary(UOp.Not, operand) =>
            booleanSideLabels(operand, flow, BoolT(!value), exprTy)
          case EBinary(BOp.Eq, left, EBool(literal)) =>
            val nextTy = BoolT(value == literal)
            if (value || exprTy(left) <= BoolT)
              booleanSideLabels(left, flow, nextTy, exprTy)
            else Set()
          case EBinary(BOp.Eq, EBool(literal), right) =>
            val nextTy = BoolT(value == literal)
            if (value || exprTy(right) <= BoolT)
              booleanSideLabels(right, flow, nextTy, exprTy)
            else Set()
          case EBinary(BOp.And, left, right) =>
            if (value)
              booleanSideLabels(left, flow, TrueT, exprTy) ++
              booleanSideLabels(right, flow, TrueT, exprTy)
            else Set()
          case EBinary(BOp.Or, left, right) =>
            if (value) Set()
            else
              booleanSideLabels(left, flow, FalseT, exprTy) ++
              booleanSideLabels(right, flow, FalseT, exprTy)
          case _ => Set()

  private def isBooleanSummaryLabel(ty: ValueTy): Boolean =
    sameTy(ty, BoolT) || sameTy(ty, NormalT(BoolT))

  private def normalizeLabels(labels: Set[ValueTy]): Set[ValueTy] =
    val hasNormalTrue = labels.exists(sameTy(_, NormalT(TrueT)))
    val hasNormalFalse = labels.exists(sameTy(_, NormalT(FalseT)))
    if (hasNormalTrue && hasNormalFalse)
      labels.filterNot(sameTy(_, NormalT(BoolT)))
    else labels

  private def resultLabels(
    before: AnalyzedCallResult,
    after: AnalyzedCallResult,
  ): Set[ValueTy] =
    val resultRefined = isStrictRefinement(before.resultTy, after.resultTy)
    val valueRefined = isStrictRefinement(before.valueTy, after.valueTy)
    val normalLabels =
      if ((after.resultTy && NormalT).isBottom) Set()
      else
        val base = if (resultRefined) Set(NormalT) else Set()
        val payload = after.valueTy
        if (
          valueRefined &&
          !payload.isBottom &&
          !payload.isTop &&
          payload.distinct(CompT)
        ) base + NormalT(payload)
        else base
    normalLabels ++
    Option.when(resultRefined)(abruptLabels(after.resultTy)).getOrElse(Set()) ++
    Option.when(resultRefined)(primitiveLabels(after.resultTy)).getOrElse(Set())

  private def traceCall(
    call: Call,
  ): (List[Set[ValueTy]], Boolean) =
    val queue = Queue.empty[(Node, Map[Local, Set[String]])]
    var seen = Set.empty[(Node, List[(Local, List[String])])]
    var branchTargetTypeSets = List.empty[Set[ValueTy]]
    var propagated = false

    def enqueue(next: Option[Node], flow: Map[Local, Set[String]]): Unit =
      next.foreach(node => queue.enqueue(node -> flow))

    def analyzedCallResult(
      checker: TyChecker,
      st: checker.AbsState,
    ): AnalyzedCallResult =
      given checker.AbsState = st
      val result = st.get(call.lhs)
      val value = st.get(result, checker.AbsValue(StrT("Value")))
      AnalyzedCallResult(result.ty, value.ty)

    def branchTargetTypes(
      branch: Branch,
      flow: Map[Local, Set[String]],
    ): Set[ValueTy] =
      val checker = tychecker
      val np = checker.NodePoint(
        cfg.funcOf(branch),
        branch,
        checker.emptyView,
      )
      val beforeSt = checker.getResult(np)
      if (beforeSt.isBottom) Set()
      else
        given checker.NodePoint[Node] = np
        val before = analyzedCallResult(checker, beforeSt)
        val (cond, condSt) = checker.transfer.transfer(branch.cond)(beforeSt)
        val condTy =
          given checker.AbsState = beforeSt
          cond.ty
        val exprTyCache = MMap.empty[Expr, ValueTy]
        def exprTy(expr: Expr): ValueTy =
          exprTyCache.getOrElseUpdate(
            expr, {
              val (value, _) = checker.transfer.transfer(expr)(beforeSt)
              given checker.AbsState = beforeSt
              value.ty
            },
          )
        Set
          .from(
            List(
              Option.when(condTy.bool.contains(true))(TrueT),
              Option.when(condTy.bool.contains(false))(FalseT),
            ).flatten.flatMap { boolTy =>
              val nextSt = checker.transfer.refine(cond, boolTy)(condSt)
              if (nextSt.isBottom) Set()
              else
                val refined =
                  resultLabels(before, analyzedCallResult(checker, nextSt))
                val booleans =
                  booleanSideLabels(branch.cond, flow, boolTy, exprTy)
                if (booleans.isEmpty) refined
                else refined.filterNot(isBooleanSummaryLabel) ++ booleans
            },
          )
          .filterNot(_.isBottom)

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
            if (exprUse(branch.cond, flow).nonEmpty) {
              val targetTypes = branchTargetTypes(branch, flow)
              val completed =
                if (branch.isAbruptNode && targetTypes.isEmpty) Set(AbruptT)
                else targetTypes
              branchTargetTypeSets ::= completed
            }
            enqueue(branch.thenNode, flow)
            enqueue(branch.elseNode, flow)
      }
    }
    branchTargetTypeSets.reverse -> propagated

  // ---------------------------------------------------------------------------
  // tests
  // ---------------------------------------------------------------------------
  def init: Unit = check("call-result splits at call sites") {
    var total = 0
    var targetTyped = 0
    var branched = 0
    var unknownBranch = 0
    var propagated = 0
    var other = 0
    val splitCounts = MMap[List[String], Int]()
    val typeCounts = MMap[String, Int]()

    for {
      func <- cfg.funcs
      calls = func.nodes.collect { case call: Call => call }.toList
      call <- calls
    } {
      total += 1
      val (branchTargetTypes, isPropagated) = traceCall(call)
      val targetTypes = normalizeLabels(branchTargetTypes.flatten.toSet)
      if (targetTypes.nonEmpty) {
        targetTyped += 1
        val split = targetTypes.toList.map(_.toString).sorted
        splitCounts += split -> (splitCounts.getOrElse(split, 0) + 1)
        for (ty <- split)
          typeCounts += ty -> (typeCounts.getOrElse(ty, 0) + 1)
      }
      if (branchTargetTypes.nonEmpty) branched += 1

      if (targetTypes.isEmpty)
        if (branchTargetTypes.nonEmpty) unknownBranch += 1
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
            "target-type-split",
            split.mkString(" | "),
            count,
            "target-types",
            targetTyped,
            percentString(count, targetTyped),
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
        "target-types",
        "(any)",
        targetTyped,
        "result-branch",
        branched,
        percentString(targetTyped, branched),
        total,
        percentString(targetTyped, total),
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

    val typeEntries = typeCounts.toList.sortBy {
      case (ty, count) => (-count, ty)
    }
    val typeRows = List(
      Vector(
        "type",
        "sites",
        "parent-class",
        "parent-sites",
        "parent-percent",
        "total-sites",
        "total-percent",
      ),
    ) ++ typeEntries.map {
      case (ty, count) =>
        Vector(
          ty,
          count,
          "target-types",
          targetTyped,
          percentString(count, targetTyped),
          total,
          percentString(count, total),
        )
    }
    dumpFile(
      typeRows.map(_.mkString("\t")).mkString(LINE_SEP),
      s"$dir/types.tsv",
    )

    val shownEntries = ListBuffer.empty[(List[String], Int)]
    var shownSites = 0
    for {
      entry @ (_, count) <- splitEntries
      if shownEntries.size < 50 &&
      (shownEntries.size < 10 || shownSites < targetTyped * 0.9)
    } {
      shownEntries += entry
      shownSites += count
    }
    val topSplits = shownEntries.map {
      case (split, count) =>
        f"      ${count}%6d/$targetTyped%-6d ${split.mkString(" | ")}"
    }
    val remaining = splitEntries.drop(shownEntries.size).map(_._2).sum
    val remainingLine =
      Option.when(remaining > 0)(
        f"      ${remaining}%6d/$targetTyped%-6d (remaining splits)",
      )
    val splitText = (topSplits ++ remainingLine).mkString("\n")
    val shownTypes = typeEntries.take(30)
    val typeText = shownTypes
      .map {
        case (ty, count) =>
          f"      ${count}%6d/$targetTyped%-6d $ty"
      }
      .mkString("\n")
    println(s"""
=== Call-result splits at call sites ===
  total call sites:         $total
  result-branch uses:       $branched/$total
    target-types:           $targetTyped/$branched
    unknown-branch:         $unknownBranch/$branched
  no result branch:         $noBranch/$total
    propagated-only:        $propagated/$noBranch
    other:                  $other/$noBranch

  top target-type splits:
    shown exact splits:     ${shownEntries.size}/${splitEntries.size}
    shown coverage:         $shownSites/$targetTyped
      sites/target           split
$splitText

  top target types:
      sites/target           type
$typeText

  dumped to $dir/summary.tsv
  dumped to $dir/types.tsv
""")
  }

  init
}
