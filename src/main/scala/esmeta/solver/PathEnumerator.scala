package esmeta.solver

import esmeta.cfg.*
import esmeta.ir.util.YetCollector

type Path = List[Node]

object PathEnumerator:
  def apply(func: Func, target: Branch): LazyList[Path] =
    if (hasYet(target)) LazyList()
    else
      // whitelist of nodes that can reach the target branch (for pruning)
      val whitelist = func.reachingTo(target)

      def succs(node: Node): List[Node] = node match
        case b: Branch if b.isLoop => Nil // TODO: support loops
        case b: Branch =>
          val thenOpt = b.thenNode.filter(whitelist)
          val elseOpt = b.elseNode.filter(whitelist)
          thenOpt.toList ++ elseOpt.toList
        case b: Block => b.next.toList
        case c: Call  => c.next.toList

      def walk(cur: Node, path: Path, visited: Set[Int]): LazyList[Path] =
        if (cur.id == target.id) LazyList(path)
        else if (hasYet(cur)) LazyList()
        else
          for {
            next <- LazyList.from(succs(cur))
            if !visited.contains(next.id)
            result <- walk(next, path :+ next, visited + next.id)
          } yield result

      walk(func.entry, List(func.entry), Set(func.entry.id)).sortBy(_.length)

  private def hasYet(node: Node): Boolean = node match
    case b: Block  => b.insts.exists(YetCollector(_).nonEmpty)
    case c: Call   => YetCollector(c.callInst).nonEmpty
    case b: Branch => YetCollector(b.cond).nonEmpty
