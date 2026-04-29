package esmeta.solver

import esmeta.cfg.*
import esmeta.ir.util.YetCollector

type Path = List[Node]

object PathEnumerator:
  def apply(func: Func, target: Branch): LazyList[Path] =
    // whitelist of nodes that can reach the target branch (for pruning)
    val whitelist = func.reachingTo(target)

    def hasYet(node: Node): Boolean = node match
      case b: Block  => b.insts.exists(YetCollector(_).nonEmpty)
      case c: Call   => YetCollector(c.callInst).nonEmpty
      case _: Branch => false

    def succs(node: Node): List[Node] = node match
      case b: Branch if b.isLoop => Nil // TODO: support loops
      case b: Branch =>
        val thenOpt = b.thenNode.filter(whitelist)
        val elseOpt = b.elseNode.filter(whitelist)
        // force then-side for builtin prefix (assume args exist)
        if (b.isBuiltinPrefix) thenOpt.orElse(elseOpt).toList
        else thenOpt.toList ++ elseOpt.toList
      case b: Block => b.next.toList
      case c: Call  => c.next.toList

    def walk(cur: Node, path: Path, visited: Set[Int]): LazyList[Path] =
      if (cur.id == target.id) LazyList(path)
      else if (hasYet(cur)) LazyList.empty // skip yet-containing paths
      else
        for {
          next <- LazyList.from(succs(cur))
          if !visited.contains(next.id)
          result <- walk(next, path :+ next, visited + next.id)
        } yield result

    walk(func.entry, List(func.entry), Set(func.entry.id)).sortBy(_.length)
