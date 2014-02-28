package dotty.tools.dotc
package transform

import scala.collection.mutable

import core._
import Phases._
import Contexts._
import Symbols._
import Decorators._
import dotty.tools.dotc.ast.untpd

/** Corresponds to lazyvals phase of scala2 */
class LocalLazyVals extends Phase {

  import ast.tpd
  import ast.Trees._

  def name = "LocalLazyVals"

  override def description =
    """Rewrites local lazy vals to classes with lazy field"""

  override def run(implicit ctx: Context): Unit = {
    val transformer = new LazyValsRewriter
    val oldTree = ctx.compilationUnit.tpdTree
    val lazyValsRewritten = transformer.transform(transformer.transform(oldTree)) // applying twice required due to rewriting all references to rewritten def

    println(s"Tree after $name is ${lazyValsRewritten.show}")
    println(s"raw representation is $lazyValsRewritten ")
    ctx.compilationUnit.tpdTree = lazyValsRewritten
  }

  class LazyValsRewriter extends tpd.TreeTransformer {

    private val localLazyValsRewritten = mutable.Map.empty[Symbol, Symbol] // this map is per-compilation-unit-per-phase
    private val classLazyValsRewritten = mutable.Map.empty[Symbol, Symbol] // this map is per-compilation-unit-per-phase

    /** Perform the following transformations:
      * - for a lazy val inside a method, replace it with a LazyHolder from
      * dotty.runtime(eg dotty.runtime.LazyInt)
      * - rewrite references to local lazy vals to field access of LazyHolder
      */
    override def transform(tree: tpd.Tree)(implicit ctx: Context): tpd.Tree = {
      def transformLocalValDef(x: tpd.ValDef) = x match {
        case x@ValDef(mods, name, tpt, rhs) =>
          val valueInitter = transform(rhs)
          val holderName = ctx.freshName(name.toString + StdNames.nme.LAZY_LOCAL).toTermName
          val tpe = x.tpe.widen

          val holderImpl =
            if (tpe == defn.IntType) ctx.requiredClass("dotty.runtime.LazyInt")
            else if (tpe == defn.LongType) ctx.requiredClass("dotty.runtime.LazyLong")
            else if (tpe == defn.BooleanType) ctx.requiredClass("dotty.runtime.LazyBoolean")
            else if (tpe == defn.FloatType) ctx.requiredClass("dotty.runtime.LazyFloat")
            else if (tpe == defn.DoubleType) ctx.requiredClass("dotty.runtime.LazyDouble")
            else if (tpe == defn.ByteType) ctx.requiredClass("dotty.runtime.LazyByte")
            else if (tpe == defn.CharType) ctx.requiredClass("dotty.runtime.LazyChar")
            else if (tpe == defn.ShortType) ctx.requiredClass("dotty.runtime.LazyShort")
            else ctx.requiredClass("dotty.runtime.LazyRef")

          val holderSymbol = ctx.newSymbol(x.symbol.owner, holderName, Flags.EmptyFlags, holderImpl.typeRef, coord = x.symbol.coord)
          // todo: is holderSymbol.pos = expr.pos required, or is cord update enough?
          val holderTree = tpd.ValDef(holderSymbol, tpd.New(holderImpl.typeRef, List(valueInitter)))
          localLazyValsRewritten += (x.symbol -> holderSymbol)
          //          ctx.debuglog(s"found a lazy val ${x.show},\n rewrote with ${holderTree.show}")
          holderTree
        // todo: is there a need\way to invalidate old symbol?
      }
      // todo: this implementation is not thread safe
      def mkSlowPathDef(methodSymbol:Symbol, target: Symbol, flag: Symbol, rhs: tpd.Tree) = {
        val cond = tpd.Ident(flag.termRef)
        val exp = tpd.Ident(target.termRef)
        val setFlag = tpd.Assign(cond, tpd.Literal(Constants.Constant(true)))
        val setTarget = tpd.Assign(exp, rhs)
        val elsep = tpd.Block(List(setFlag, setTarget), exp)
        tpd.If(cond, exp, elsep)
      }

      def mkDef(methodSymbol: TermSymbol, claz:ClassSymbol, target: Symbol, rhs:tpd.Tree, tp:Types.Type, getFlag:Symbol, casFlag:Symbol, setFlagState:Symbol, waitOnLock: Symbol) = {

        val initState = tpd.Literal(Constants.Constant(0))
        val computeState = tpd.Literal(Constants.Constant(1))
        val notifyState = tpd.Literal(Constants.Constant(2))
        val computedState = tpd.Literal(Constants.Constant(3))
        val thiz = tpd.This(claz)

        val resultSymbol = ctx.newSymbol(methodSymbol, "result".toTermName, Flags.Mutable, tp)
        val resultDef = tpd.ValDef(resultSymbol)

        val setFlagSymbol = ctx.newSymbol(methodSymbol, "retry".toTermName, Flags.Mutable, defn.BooleanType)
        val setFlagDef = tpd.ValDef(resultSymbol, tpd.Literal(Constants.Constant(true)))

        val whileCond = tpd.Ident(setFlagSymbol.termRef)

        val compute = {


          // val eSymbol = ctx.newSymbol(methodSymbol, "e".toTermName, Flags.EmptyFlags, defn.ThrowableType)
          // val pattern = tpd.Bind(eSymbol, )
          // val failed =tpd.CaseDef()
          // TRY
          val compute = tpd.Assign(tpd.Ident(resultSymbol.termRef), rhs)
          val assign = tpd.Assign(tpd.Ident(target.termRef), tpd.Ident(resultSymbol.termRef))
          val complete = tpd.Apply(tpd.Ident(setFlagState.termRef), List(thiz, computedState))
          val noRetry = tpd.Assign(tpd.Ident(setFlagSymbol.termRef), tpd.Literal(Constants.Constant(false)))
          val body = tpd.If(tpd.Apply(tpd.Ident(casFlag.termRef), List(thiz, initState, computeState)),
            tpd.Block(compute::complete::noRetry::assign::Nil, tpd.EmptyTree), // todo:return Unit?
            tpd.EmptyTree)

          tpd.CaseDef(initState, tpd.EmptyTree, body)
        }

        val waitFirst = {
          val wait = tpd.Apply(tpd.Ident(waitOnLock.termRef), List(thiz, computeState))
          tpd.CaseDef(computeState, tpd.EmptyTree, wait)
        }

        val waitSecond = {
          val wait = tpd.Apply(tpd.Ident(waitOnLock.termRef), List(thiz, notifyState))
          tpd.CaseDef(notifyState, tpd.EmptyTree, wait)
        }

        val computed = {
          val noRetry = tpd.Assign(tpd.Ident(setFlagSymbol.termRef), tpd.Literal(Constants.Constant(false)))
          val result = tpd.Assign(tpd.Ident(resultSymbol.termRef), tpd.Ident(target.termRef))
          val body = tpd.Block(noRetry::result::Nil, tpd.EmptyTree) // todo:return Unit?
          tpd.CaseDef(notifyState, tpd.EmptyTree, body)
        }



        val cases = tpd.Match(tpd.Apply(tpd.Ident(getFlag.termRef), List(thiz)), List(compute, waitFirst, waitSecond, computed)) //todo: annotate with @switch

        val cycle = untpd.WhileDo(whileCond, cases).withTypeUnchecked(defn.UnitType)

        tpd.DefDef(methodSymbol, tpd.Block(resultDef::setFlagDef::cycle::Nil, tpd.Ident(resultSymbol.termRef)))
      }

      def transformIdent(expr: tpd.Ident) = {
        val rewr1 = localLazyValsRewritten.get(expr.symbol) match {
          case Some(newSymbol) =>
            val ident = tpd.Ident(newSymbol.termRef)
            tpd.Select(ident, "value".toTermName)
          case None => expr
        }
        val rewr2 = classLazyValsRewritten.get(rewr1.symbol) match {
          case Some(newSymbol) =>
            val ident = tpd.Ident(newSymbol.termRef)
            tpd.Apply(ident, Nil)
          case None => expr
        }
        rewr2
      }

      tree match {
        case Block(stats, expr) =>
          val newStats = stats.mapConserve {
            case t@ValDef(mods, _, _, _) if (mods is Flags.Lazy) =>
              transformLocalValDef(t)
            case t: tpd.Ident =>
              transformIdent(t)
            case expr => super.transform(expr)
          }
          val newExpr = transform(expr)
          if ((newExpr eq expr) && (newStats eq stats)) tree
          else tpd.Block(newStats, newExpr)
        case TypeDef(mods, name, rhs) if tree.symbol.isClass =>
          val template = rhs.asInstanceOf[tpd.Template]
          val body = template.body
          // todo: also take care of lazy vals defined in parents
          val lazyValsCount = body.count {
            case ValDef(mods, _, _, _) if mods is Flags.Lazy => true
            case _ => false
          }
          if (lazyValsCount == 0) super.transform(tree)
          else {
            var ord = 0
            val newBody = body.flatMap {
              case x@ValDef(mods, name, tpt, orhs) if (mods is Flags.Lazy) =>
                val rhs = transform(orhs)
                val tpe = x.tpe.widen
                assert(!(mods is Flags.Mutable))
                val containerName = ctx.freshName(name.toString + StdNames.nme.LAZY_LOCAL).toTermName
                val containerSymbol = ctx.newSymbol(x.symbol.owner, containerName, (mods &~ Flags.Lazy).flags, tpe, coord = x.symbol.coord)
                // todo: is holderSymbol.pos = expr.pos required, or is cord update enough?
                val containerTree = tpd.ValDef(containerSymbol, tpd.Literal(Constants.Constant(0))) //todo: tpd.Ident(_)?
                val flagName = ctx.freshName(name.toString + StdNames.nme.BITMAP_PREFIX).toTermName
                val flagSymbol = ctx.newSymbol(x.symbol.owner, flagName, Flags.EmptyFlags, defn.BooleanType)
                val flag = tpd.ValDef(flagSymbol, tpd.Literal(Constants.Constant(false)))
                val slowPathName = name
                val slowPathSymbol = ctx.newSymbol(x.symbol.owner, slowPathName, Flags.EmptyFlags, tpe)
                val slowPath = tpd.DefDef(slowPathSymbol, mkSlowPathDef(slowPathSymbol, containerSymbol, flagSymbol, rhs))
                classLazyValsRewritten += (x.symbol -> slowPathSymbol)
                ord += 1
                List(containerTree, flag, slowPath)
              case x => List(transform(x))
            }

            super.transform(tpd.ClassDef(tree.symbol.asClass, template.constr, newBody))
          }
        case t: tpd.Ident =>
          transformIdent(t)
        case _ => super.transform(tree)
      }
    }
  }


}

