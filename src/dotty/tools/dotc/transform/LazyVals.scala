package dotty.tools.dotc.transform

import scala.collection.mutable
import dotty.tools.dotc._
import core._
import Contexts._
import Symbols._
import Decorators._
import NameOps._
import dotty.tools.dotc.transform.TreeTransforms.{TransformerInfo, TreeTransformer, TreeTransform}
import dotty.tools.dotc.ast.Trees._
import dotty.tools.dotc.ast.{untpd, tpd}
import dotty.tools.dotc.core.Constants.Constant
import dotty.tools.dotc.core.Types.MethodType
import dotty.tools.dotc.core.Names.Name
import dotty.tools.dotc.transform.PostTyperTransformers.{CompanionNeededPredicate, CompanionObjectNeeded}

class LazyValTranformContext(group: TreeTransformer, idx: Int) {

  import tpd._

  /** this map contains mutable state of transformation: OffsetDefs to be appended to companion object definitions */
  val appendOffsetDefs: mutable.Map[Name, Tree] = mutable.Map.empty
  val transformer = new LazyValsTransform()

  class LazyValsTransform() extends TreeTransform(group, idx) with CompanionObjectNeeded {

    /** Companion classes are required to hold offsets for volatile lazy vals */
    override def companionObjectRequiredPredicate = new CompanionNeededPredicate {
      def apply(forClass: tpd.TypeDef)(implicit ctx: Context): Boolean = {
        (!(forClass.symbol is Flags.Module)) && forClass.rhs.isInstanceOf[Template] && {
          val body = forClass.rhs.asInstanceOf[Template].body
          body.exists {
            case x: ValDef =>
              (x.mods is Flags.Lazy) && x.mods.annotations.exists(_.tpe == defn.VolatileAnnotType)
            case _ => false
          }
        }
      }
    }

    override def transformValDef(tree: tpd.ValDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
      if (!(tree.mods is Flags.Lazy)) tree
      else {
        val isField = tree.symbol.owner.isClass
        val isVolatile = tree.mods.annotations.exists(_.tpe == defn.VolatileAnnotType)

        if (isField) {
          if (isVolatile) transformFieldValDefVolatile(tree)
          else transformFieldValDefNonVolatile(tree)
        }
        else transformLocalValDef(tree)

      }
    }

    override def transformTypeDef(tree: tpd.TypeDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
      if (!tree.symbol.isClass) tree
      else {
        appendOffsetDefs.get(tree.symbol.name) match {
          case None => tree
          case Some(data) =>
            val template = tree.rhs.asInstanceOf[Template]
            tpd.ClassDef(tree.symbol.asClass, template.constr, transformFollowingDeep(data) :: template.body)
        }
      }
    }
    /** Replace a local lazy val inside a method, 
      * with a LazyHolder from
      * dotty.runtime(eg dotty.runtime.LazyInt)
      */
    def transformLocalValDef(x: ValDef)(implicit ctx: Context) = x match {
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

        val holderSymbol = ctx.newSymbol(x.symbol.owner, holderName, Flags.Synthetic, holderImpl.typeRef, coord = x.symbol.coord)
        // todo: is holderSymbol.pos = expr.pos required, or is cord update enough?
        val holderTree = tpd.ValDef(holderSymbol, tpd.New(holderImpl.typeRef, List(valueInitter)))
        val methodTree = tpd.DefDef(x.symbol.asTerm, tpd.Select(tpd.Ident(holderSymbol.termRef), "value".toTermName))
        ctx.debuglog(s"found a lazy val ${x.show},\n rewrote with ${holderTree.show}")
        tpd.Thicket(holderTree, methodTree)
    }

    /** Create non-threadsafe lazy accessor equivalent to such code
      * def methodSymbol() = {
      * if (flag) target
      * else {
      * target = rhs
      * flag = true
      * target
      * }
      * }
      */

    def mkNonThreadSafeDef(methodSymbol: Symbol, target: Symbol, flag: Symbol, rhs: tpd.Tree)(implicit ctx: Context) = {
      val cond = tpd.Ident(flag.termRef)
      val exp = tpd.Ident(target.termRef)
      val setFlag = tpd.Assign(cond, tpd.Literal(Constants.Constant(true)))
      val setTarget = tpd.Assign(exp, rhs)
      val elsep = tpd.Block(List(setFlag, setTarget), exp)
      tpd.If(cond, exp, elsep)
    }

    def initValue(tpe: Types.Type)(implicit ctx: Context) = tpe match {
      case tpe if tpe == defn.IntType => Constant(0)
      case tpe if tpe == defn.LongType => Constant(0L)
      case tpe if tpe == defn.BooleanType => Constant(false)
      case tpe if tpe == defn.CharType => Constant('\u0000')
      case tpe if tpe == defn.FloatType => Constant(0f)
      case tpe if tpe == defn.DoubleType => Constant(0d)
      case tpe if tpe == defn.ByteType => Constant(0.toByte)
      case _ => Constant(null)
    }

    def transformFieldValDefNonVolatile(x: ValDef)(implicit ctx: Context) = x match {
      case x@ValDef(mods, name, tpt, rhs) if (mods is Flags.Lazy) =>
        val tpe = x.tpe.widen
        assert(!(mods is Flags.Mutable))
        val containerName = ctx.freshName(name.toString + StdNames.nme.LAZY_LOCAL).toTermName
        val containerSymbol = ctx.newSymbol(x.symbol.owner, containerName, (mods &~ Flags.Lazy).flags, tpe, coord = x.symbol.coord).entered

        val containerTree = tpd.ValDef(containerSymbol, Literal(initValue(tpe)))
        val flagName = ctx.freshName(name.toString + StdNames.nme.BITMAP_PREFIX).toTermName
        val flagSymbol = ctx.newSymbol(x.symbol.owner, flagName, Flags.EmptyFlags, defn.BooleanType)
        val flag = tpd.ValDef(flagSymbol, tpd.Literal(Constants.Constant(false)))
        val slowPathName = name
        val slowPathSymbol = ctx.newSymbol(x.symbol.owner, slowPathName, Flags.EmptyFlags, tpe).entered
        val slowPath = tpd.DefDef(x.symbol.asTerm, mkNonThreadSafeDef(slowPathSymbol, containerSymbol, flagSymbol, rhs))
        Thicket(List(containerTree, flag, slowPath))
    }

    /** Create non-threadsafe lazy accessor equivalent to such code
      *
      * def methodSymbol(): Int = {
      * val result: Int = 0
      * val retry: Boolean = true
      * var flag: Long = 0L
      * while retry do {
      * flag = dotty.runtime.LazyVals.get(this, $claz.$OFFSET)
      * dotty.runtime.LazyVals.STATE(flag, 0) match {
      * case 0 =>
      * if dotty.runtime.LazyVals.CAS(this, $claz.$OFFSET, flag, 1, $ord) then
      * {
      * try {result = rhs} catch {
      * case x: Throwable =>
      * dotty.runtime.LazyVals.setFlag(this, $claz.$OFFSET, 0, $ord)
      * throw x$1
      * }
      * $target = result
      * dotty.runtime.LazyVals.setFlag(this, $claz.$OFFSET, 3, $ord)
      * retry = false
      * ()
      * }
      * else ()
      * case 1 =>
      * dotty.runtime.LazyVals.wait4Notification(this, $claz.$OFFSET, flag, $ord)
      * case 2 =>
      * dotty.runtime.LazyVals.wait4Notification(this, $claz.$OFFSET, flag, $ord)
      * case 3 =>
      * retry = false
      * result = $target
      * ()
      * }
      * }
      * result
      * }
      */
    def mkThreadSafeDef(methodSymbol: TermSymbol, claz: ClassSymbol, ord: Int, target: Symbol, rhs: tpd.Tree, tp: Types.Type, offset: Tree, getFlag: Tree, stateMask: Tree, casFlag: Tree, setFlagState: Tree, waitOnLock: Tree)(implicit ctx: Context) = {
      val initState = tpd.Literal(Constants.Constant(0))
      val computeState = tpd.Literal(Constants.Constant(1))
      val notifyState = tpd.Literal(Constants.Constant(2))
      val computedState = tpd.Literal(Constants.Constant(3))
      val flagSymbol = ctx.newSymbol(methodSymbol, "flag".toTermName, Flags.Mutable, defn.LongType)
      val flagDef = tpd.ValDef(flagSymbol, Literal(Constant(0L)))

      val thiz = tpd.This(claz)(ctx.fresh.withOwner(claz))

      val resultSymbol = ctx.newSymbol(methodSymbol, "result".toTermName, Flags.Mutable, tp)
      val resultDef = tpd.ValDef(resultSymbol, Literal(initValue(tp.widen)))

      val retrySymbol = ctx.newSymbol(methodSymbol, "retry".toTermName, Flags.Mutable, defn.BooleanType)
      val retryDef = tpd.ValDef(retrySymbol, tpd.Literal(Constants.Constant(true)))

      val whileCond = tpd.Ident(retrySymbol.termRef)

      val compute = {
        val handlerSymbol = ctx.newSymbol(methodSymbol, "$anonfun".toTermName, Flags.Synthetic,
          MethodType(List("x$1".toTermName), List(defn.ThrowableType), defn.IntType))


        val handler = tpd.Closure(handlerSymbol, {
          args =>
            val exception = args.head.head
            val complete = tpd.Apply(setFlagState, List(thiz, offset, initState, Literal(Constant(ord))))
            tpd.Block(List(complete), tpd.Throw(exception))

        })


        val compute = tpd.Assign(tpd.Ident(resultSymbol.termRef), rhs)
        val tr = tpd.Try(compute, handler, EmptyTree)
        val assign = tpd.Assign(tpd.Ident(target.termRef), tpd.Ident(resultSymbol.termRef))
        val complete = tpd.Apply(setFlagState, List(thiz, offset, computedState, Literal(Constant(ord))))
        val noRetry = tpd.Assign(tpd.Ident(retrySymbol.termRef), tpd.Literal(Constants.Constant(false)))
        val body = tpd.If(tpd.Apply(casFlag, List(thiz, offset, tpd.Ident(flagSymbol.termRef), computeState, tpd.Literal(Constant(ord)))),
          tpd.Block(tr :: assign :: complete :: noRetry :: Nil, tpd.Literal(Constant(()))),
          tpd.Literal(Constant(())))

        tpd.CaseDef(initState, tpd.EmptyTree, body)
      }

      val waitFirst = {
        val wait = tpd.Apply(waitOnLock, List(thiz, offset, tpd.Ident(flagSymbol.termRef), Literal(Constant(ord))))
        tpd.CaseDef(computeState, tpd.EmptyTree, wait)
      }

      val waitSecond = {
        val wait = tpd.Apply(waitOnLock, List(thiz, offset, tpd.Ident(flagSymbol.termRef), Literal(Constant(ord))))
        tpd.CaseDef(notifyState, tpd.EmptyTree, wait)
      }

      val computed = {
        val noRetry = tpd.Assign(tpd.Ident(retrySymbol.termRef), tpd.Literal(Constants.Constant(false)))
        val result = tpd.Assign(tpd.Ident(resultSymbol.termRef), tpd.Ident(target.termRef))
        val body = tpd.Block(noRetry :: result :: Nil, tpd.Literal(Constant(())))
        tpd.CaseDef(computedState, tpd.EmptyTree, body)
      }

      val cases = tpd.Match(tpd.Apply(stateMask, List(tpd.Ident(flagSymbol.termRef), tpd.Literal(Constant(ord)))),
        List(compute, waitFirst, waitSecond, computed)) //todo: annotate with @switch

      val whileBody = tpd.Block(List(tpd.Assign(tpd.Ident(flagSymbol.termRef), tpd.Apply(getFlag, List(thiz, offset)))), cases)
      val cycle = untpd.WhileDo(whileCond, whileBody).withTypeUnchecked(defn.UnitType)
      tpd.DefDef(methodSymbol, tpd.Block(resultDef :: retryDef :: flagDef :: cycle :: Nil, tpd.Ident(resultSymbol.termRef)))
    }

    def transformFieldValDefVolatile(x: ValDef)(implicit ctx: Context) = x match {
      case x@ValDef(mods, name, tpt, rhs) if (mods is Flags.Lazy) =>
        // todo: allow multiple lazy vals to share flag
        val ord = 0
        val tpe = x.tpe.widen
        val claz = x.symbol.owner.asClass
        assert(!(mods is Flags.Mutable))
        val helperModule = ctx.requiredModule("dotty.runtime.LazyVals")
        val containerName = ctx.freshName(name.toString + StdNames.nme.LAZY_LOCAL).toTermName
        val containerSymbol = ctx.newSymbol(claz, containerName, (mods &~ Flags.Lazy & Flags.Synthetic).flags, tpe, coord = x.symbol.coord).entered
        val containerTree = tpd.ValDef(containerSymbol, Literal(initValue(tpe)))


        val flagName = ctx.freshName(name.toString + StdNames.nme.BITMAP_PREFIX).toTermName
        val flagSymbol = ctx.newSymbol(claz, flagName, Flags.Synthetic, defn.LongType).entered
        val flag = tpd.ValDef(flagSymbol, tpd.Literal(Constants.Constant(0L)))

        val thiz = tpd.This(claz)(ctx.fresh.withOwner(claz))

        val companion = claz.companionModule

        val getOffset = tpd.Select(tpd.Ident(helperModule.termRef), "getOffset".toTermName)

        val offsetSymbol = ctx.newSymbol(companion.moduleClass, (name.toString + StdNames.nme.LAZY_FIELD_OFFSET).toTermName, Flags.Synthetic, defn.LongType).entered
        val offsetTree: Tree = tpd.ValDef(offsetSymbol, tpd.Apply(getOffset, List(thiz, Literal(Constant(flagName.toString)))))
        val offset = Select(Ident(companion.termRef), offsetSymbol.name)
        appendOffsetDefs += (companion.name.moduleClassName -> offsetTree)

        val getFlag = tpd.Select(tpd.Ident(helperModule.termRef), "get".toTermName)
        val setFlag = tpd.Select(tpd.Ident(helperModule.termRef), "setFlag".toTermName)
        val wait = tpd.Select(tpd.Ident(helperModule.termRef), "wait4Notification".toTermName)
        val state = tpd.Select(tpd.Ident(helperModule.termRef), "STATE".toTermName)
        val cas = tpd.Select(tpd.Ident(helperModule.termRef), "CAS".toTermName)

        val accessor = mkThreadSafeDef(x.symbol.asTerm, claz, ord, containerSymbol, rhs, x.tpe, offset, getFlag, state, cas, setFlag, wait)
        Thicket(List(containerTree, flag, accessor))
    }
  }

}



