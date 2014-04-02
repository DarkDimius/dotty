package test

import scala.reflect.io._
import dotty.tools.dotc.util._
import dotty.tools.dotc.core._
import dotty.tools.dotc.parsing._
import Tokens._, Parsers._
import dotty.tools.dotc._
import ast.Trees._
import ast.desugar
import ast.desugar._
import typer.Mode
import Contexts.Context

import scala.collection.mutable.ListBuffer

class DeSugarTest extends ParserTest {

  import dotty.tools.dotc.ast.untpd._

  import Mode._

  val Expr = Mode(0)

  object DeSugar extends UntypedTreeMap {
    var curMode: Mode = Expr
    def withMode[T](mode: Mode)(op: => T) = {
      val saved = curMode
      curMode = mode
      try op
      finally curMode = saved
    }

    def transform(tree: Tree, mode: Mode)(implicit ctx: Context): Tree = withMode(mode) { transform(tree) }
    def transform(trees: List[Tree], mode: Mode)(implicit ctx: Context): List[Tree] = withMode(mode) { transform(trees) }

    override def transform(tree: Tree)(implicit ctx: Context): Tree = {
      val tree1 = desugar(tree)(ctx.withMode(curMode))
      tree1 match {
        case TypedSplice(t) =>
          tree1
        case PostfixOp(od, op) =>
          PostfixOp(transform(od), op)
        case Select(qual, name) =>
          cpy.Select(tree1, transform(qual, Expr), name)
        case Apply(fn, args) =>
          cpy.Apply(tree1, transform(fn, Expr), transform(args))
        case TypeApply(fn, args) =>
          cpy.TypeApply(tree1, transform(fn, Expr), transform(args, Type))
        case New(tpt) =>
          cpy.New(tree1, transform(tpt, Type))
        case Typed(expr, tpt) =>
          cpy.Typed(tree1, transform(expr), transform(tpt, Type))
        case CaseDef(pat, guard, body) =>
          cpy.CaseDef(tree1, transform(pat, Pattern), transform(guard), transform(body))
        case SeqLiteral(elems) =>
          cpy.SeqLiteral(tree1, transform(elems))
        case UnApply(fun, implicits, patterns) =>
          cpy.UnApply(tree1, transform(fun, Expr), transform(implicits), transform(patterns))
        case ValDef(mods, name, tpt, rhs) =>
          cpy.ValDef(tree1, mods, name, transform(tpt, Type), transform(rhs))
        case DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
          cpy.DefDef(tree1, mods, name, transformSub(tparams), vparamss mapConserve (transformSub(_)), transform(tpt, Type), transform(rhs))
        case tree1 @ TypeDef(mods, name, rhs) =>
          cpy.TypeDef(tree1, mods, name, transform(rhs, Type), transformSub(tree1.tparams))
        case Template(constr, parents, self, body) =>
          cpy.Template(tree1, transformSub(constr), transform(parents), transformSub(self), transform(body, Expr))
        case Thicket(trees) =>
          Thicket(flatten(trees mapConserve super.transform))
        case tree1 =>
          super.transform(tree1)
      }
    }
  }

  def firstClass(stats: List[Tree]): String = stats match {
    case Nil => "<empty>"
    case TypeDef(_, name, _) :: _ => name.toString
    case ModuleDef(_, name, _) :: _ => name.toString
    case (pdef: PackageDef) :: _ => firstClass(pdef)
    case stat :: stats => firstClass(stats)
  }

  def firstClass(tree: Tree): String = tree match {
    case PackageDef(pid, stats) =>
      pid.show + "." + firstClass(stats)
    case _ => "??? "+tree.getClass
  }

  def desugarTree(tree: Tree): Tree = {
    //println("***** desugaring "+firstClass(tree))
    DeSugar.transform(tree)
  }

  def desugarAll() = parsedTrees foreach (desugarTree(_).show)
}
