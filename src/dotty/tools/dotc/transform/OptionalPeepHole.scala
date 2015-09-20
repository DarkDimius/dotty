package dotty.tools.dotc
package transform

import core._
import Contexts._, Symbols._, Types._, Flags._, Decorators._, StdNames._, Constants._, Phases._
import TreeTransforms._
import ast.Trees._
import dotty.tools.dotc.ast.{TreeTypeMap, tpd}
import dotty.tools.dotc.core.DenotTransformers.InfoTransformer
import dotty.tools.dotc.core.Names.{TermName, Name}
import collection.mutable

class OptionalPeepHole extends MiniPhaseTransform { thisTransformer =>
  import tpd._
  import dotty.tools.dotc.transform.Optional._

  def phaseName: String = "OptionalPeepHole"

  override def transformSelect(tree: tpd.Select)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    if (tree.symbol.owner.derivesFrom(OptionalClaz))
      unwrap(tree)
    else tree
  }

  override def transformIdent(tree: tpd.Ident)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    if (tree.symbol.owner.derivesFrom(OptionalClaz))
      unwrap(tree)
    else tree
  }

  def unwrap(t: Tree)(implicit ctx: Context) = t match {
    case Select(t: Apply, name) if t.fun.symbol == OptionalApply =>
      name.toString match {
        case "isEmpty" =>
          t.args.head
        case "underlying" | "get" =>
          t.args.tail.head
        case _ =>
          t
      }
    case Select(t: Apply, name) if t.fun.symbol == SomeApply =>
      name.toString match {
        case "isEmpty" =>
          Literal(Constant(false))
        case "underlying" | "get" =>
          t.args.head
        case _ =>
          t
      }
    case _ => t
  }

  override def transformApply(tree: tpd.Apply)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    if (tree.fun.symbol.owner.derivesFrom(OptionalClaz)) {
      unwrap(tree)
    } else tree
  }
}

