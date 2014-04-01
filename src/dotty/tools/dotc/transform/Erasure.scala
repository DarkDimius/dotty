package dotty.tools.dotc
package transform

import core.Phases._
import core.DenotTransformers._
import core.Denotations._
import core.SymDenotations._
import core.Symbols._
import core.Contexts._
import core.Types._
import core.Names._
import core.StdNames._
import core.NameOps._
import core.Decorators._
import core.Constants._
import typer.NoChecking
import typer.ProtoTypes._
import typer.ErrorReporting._
import core.transform.Erasure._
import core.Decorators._
import ast.{tpd, untpd}
import ast.Trees._
import dotty.tools.dotc.core.Scopes

class Erasure extends Phase with DenotTransformer {

  override def name: String = "erasure"

  def transform(ref: SingleDenotation)(implicit ctx: Context): SingleDenotation = ref match {
    case ref: SymDenotation =>
      assert(ctx.phase == this, s"transforming $ref at ${ctx.phase}")
      ref.copySymDenotation(info = transformInfo(ref.symbol, ref.info))
    case ref =>
      ref.derivedSingleDenotation(ref.symbol, erasure(ref.info))
  }

  val eraser = new Erasure.Typer

  def run(implicit ctx: Context): Unit = {
    val unit = ctx.compilationUnit
    unit.tpdTree = eraser.typedExpr(unit.tpdTree)(ctx.fresh.setPhase(this.next))
  }
}

object Erasure {

  import tpd._

  object Boxing {

    def isUnbox(sym: Symbol)(implicit ctx: Context) =
      sym.name == nme.unbox && (defn.ScalaBoxedClasses contains sym.owner)

    def isBox(sym: Symbol)(implicit ctx: Context) =
      sym.name == nme.box && (defn.ScalaValueClasses contains sym.owner)

    def boxMethod(cls: ClassSymbol)(implicit ctx: Context) =
      cls.linkedClass.info.member(nme.box).symbol
    def unboxMethod(cls: ClassSymbol)(implicit ctx: Context) =
      cls.linkedClass.info.member(nme.unbox).symbol

    /** Isf this tree is an unbox operation which can be safely removed
     *  when enclosed in a box, the unboxed argument, otherwise EmptyTree.
     *  Note that one can't always remove a Box(Unbox(x)) combination because the
     *  process of unboxing x may lead to throwing an exception.
     *  This is important for specialization: calls to the super constructor should not box/unbox specialized
     *  fields (see TupleX). (ID)
     */
    private def safelyRemovableUnboxArg(tree: Tree)(implicit ctx: Context): Tree = tree match {
      case Apply(fn, arg :: Nil)
      if isUnbox(fn.symbol) && (defn.ScalaBoxedClasses contains arg.tpe.widen.typeSymbol) =>
        arg
      case _ =>
        EmptyTree
    }

    def isErasedValueType(tpe: Type)(implicit ctx: Context): Boolean = tpe.isInstanceOf[ErasedValueType]
    def isPrimitiveValueType(tpe: Type)(implicit ctx: Context): Boolean = tpe.classSymbol.isPrimitiveValueClass

    def constant(tree: Tree, const: Tree)(implicit ctx: Context) =
      if (isIdempotentExpr(tree)) Block(tree :: Nil, const) else const

    final def box(tree: Tree, target: => String = "")(implicit ctx: Context): Tree = ctx.traceIndented(i"boxing ${tree.showSummary}: ${tree.tpe} into $target") {
      tree.tpe.widen match {
        case ErasedValueType(clazz, _) =>
          New(clazz.typeRef, cast(tree, clazz.underlyingOfValueClass) :: Nil) // todo: use adaptToType?
        case tp =>
          val cls = tp.classSymbol
          if (cls eq defn.UnitClass) constant(tree, ref(defn.BoxedUnit_UNIT))
          else if (cls eq defn.NothingClass) tree // a non-terminating expression doesn't need boxing
          else {
            assert(cls ne defn.ArrayClass)
            val arg = safelyRemovableUnboxArg(tree)
            if (arg.isEmpty) Apply(ref(boxMethod(cls.asClass)), tree :: Nil)
            else {
              ctx.log(s"boxing an unbox: ${tree.symbol} -> ${arg.tpe}")
              arg
            }
          }
      }
    }

    def unbox(tree: Tree, pt: Type)(implicit ctx: Context): Tree = ctx.traceIndented(i"unboxing ${tree.showSummary}: ${tree.tpe} as a $pt") {
      pt match {
        case ErasedValueType(clazz, underlying) =>
          val tree1 =
            if ((tree.tpe isRef defn.NullClass) && isPrimitiveValueType(underlying))
              // convert `null` directly to underlying type, as going
              // via the unboxed type would yield a NPE (see SI-5866)
              unbox(tree, underlying)
            else
              Apply(Select(adaptToType(tree, clazz.typeRef), clazz.valueClassUnbox), Nil)
          cast(tree1, pt)
        case _ =>
          val cls = pt.classSymbol
          if (cls eq defn.UnitClass) constant(tree, Literal(Constant(())))
          else {
            assert(cls ne defn.ArrayClass)
            Apply(ref(unboxMethod(cls.asClass)), tree :: Nil)
          }
      }
    }

    /** Generate a synthetic cast operation from tree.tpe to pt.
     */
    def cast(tree: Tree, pt: Type)(implicit ctx: Context): Tree =
      if (pt isRef defn.UnitClass) unbox(tree, pt)
      else (tree.tpe, pt) match {
        case (defn.ArrayType(treeElem), defn.ArrayType(ptElem))
        if isPrimitiveValueType(treeElem.widen) && !isPrimitiveValueType(ptElem) =>
          // See SI-2386 for one example of when this might be necessary.
          cast(runtimeCall(nme.toObjectArray, tree :: Nil), pt)
        case _ =>
          ctx.log(s"casting from ${tree.showSummary}: ${tree.tpe.show} to ${pt.show}")
          TypeApply(Select(tree, defn.Object_asInstanceOf), TypeTree(pt) :: Nil)
      }

    /** Adaptation of an expression `e` to an expected type `PT`, applying the following
     *  rewritings exhaustively as long as the type of `e` is not a subtype of `PT`.
     *
     *    e -> box(e)        if `e` is of erased value type
     *    e -> unbox(e, PT)  otherwise, if `PT` is an erased value type
     *    e -> box(e)        if `e` is of primitive type and `PT` is not a primitive type
     *    e -> unbox(e, PT)  if `PT` is a primitive type and `e` is not of primitive type
     *    e -> cast(e, PT)   otherwise
     */
    def adaptToType(tree: Tree, pt: Type)(implicit ctx: Context): Tree =
      if (tree.tpe <:< pt)
        tree
      else if (isErasedValueType(tree.tpe.widen))
        adaptToType(box(tree), pt)
      else if (isErasedValueType(pt))
        adaptToType(unbox(tree, pt), pt)
      else if (isPrimitiveValueType(tree.tpe.widen) && !isPrimitiveValueType(pt))
        adaptToType(box(tree), pt)
      else if (isPrimitiveValueType(pt) && !isPrimitiveValueType(tree.tpe.widen))
        adaptToType(unbox(tree, pt), pt)
      else
        cast(tree, pt)
  }

  class Typer extends typer.ReTyper with NoChecking {
    import Boxing._

    def erasedType(tree: untpd.Tree)(implicit ctx: Context): Type = erasure(tree.typeOpt)

    override def promote(tree: untpd.Tree)(implicit ctx: Context): tree.ThisTree[Type] = {
      assert(tree.hasType)
      val erased = erasedType(tree)(ctx.withPhase(ctx.erasurePhase))
      ctx.log(s"promoting ${tree.show}: ${erased.showWithUnderlying()}")
      tree.withType(erased)
    }

    /** Type check select nodes, applying the following rewritings exhaustively
     *  on selections `e.m`.
     *
     *      e.m1 -> e.m2        if `m1` is a member of Any or AnyVal and `m2` is
     *                          the same-named member in Object.
     *      e.m -> box(e).m     if `e` is primitive and `m` is a member or a reference class
     *                          or `e` has an erased value class type.
     *      e.m -> unbox(e).m   if `e` is not primitive and `m` is a member of a primtive type.
     *
     *  Additionally, if the type of `e` does not derive from the type `OT` of the owner of `m`,
     *  the following rewritings are performed, where `ET` is the erased type of the selection's
     *  original qualifier expression.
     *
     *      e.m -> cast(OT).m   if `m` is not an array operation
     *      e.m -> cast(ET).m   if `m` is an array operation and `ET` is an array type
     *      e.m -> runtime.array_m(e)
     *                          if `m` is an array operation and `ET` is Object
     */
    override def typedSelect(tree: untpd.Select, pt: Type)(implicit ctx: Context): Tree = {
      val sym = tree.symbol
      assert(sym.exists)

      def select(qual: Tree, sym: Symbol): Tree =
        untpd.cpy.Select(tree, qual, sym.name) withType qual.tpe.select(sym)

      def selectArrayMember(qual: Tree, erasedPre: Type) =
        if (erasedPre isRef defn.ObjectClass) runtimeCall(tree.name.genericArrayOp, qual :: Nil)
        else recur(cast(qual, erasedPre))

      def recur(qual: Tree): Tree = {
        val qualIsPrimitive = isPrimitiveValueType(qual.tpe)
        val symIsPrimitive = sym.owner.isPrimitiveValueClass
        if ((sym.owner eq defn.AnyClass) || (sym.owner eq defn.AnyValClass))
          select(qual, defn.ObjectClass.info.decl(sym.name).symbol)
        else if (qualIsPrimitive && !symIsPrimitive || isErasedValueType(qual.tpe))
          recur(box(qual))
        else if (!qualIsPrimitive && symIsPrimitive)
          recur(unbox(qual, sym.owner.typeRef))
        else if (qual.tpe.derivesFrom(sym.owner) || qual.isInstanceOf[Super])
          select(qual, sym)
        else if (sym.owner eq defn.ArrayClass)
          selectArrayMember(qual, erasure(tree.qualifier.tpe))
        else
          recur(cast(qual, sym.owner.typeRef))
      }

      recur(typed(tree.qualifier, AnySelectionProto))
    }

    override def typedTypeApply(tree: untpd.TypeApply, pt: Type)(implicit ctx: Context) = {
      val TypeApply(fun, args) = tree
      val fun1 = typedExpr(fun, pt)
      fun1.tpe.widen match {
        case funTpe: PolyType =>
          val args1 = args.mapconserve(typedType(_))
          untpd.cpy.TypeApply(tree, fun1, args1).withType(funTpe.instantiate(args1.tpes))
        case _ => fun1
      }
    }

    override def typedApply(tree: untpd.Apply, pt: Type)(implicit ctx: Context): Tree = {
      val Apply(fun, args) = tree
      val fun1 = typedExpr(fun, WildcardType)
      fun1.tpe.widen match {
        case mt: MethodType =>
          val args1 = args.zipWithConserve(mt.paramTypes)(typedExpr)
          untpd.cpy.Apply(tree, fun1, args1) withType mt.resultType
      }
    }

    override def typedTypeTree(tree: untpd.TypeTree, pt: Type)(implicit ctx: Context): TypeTree =
      promote(tree)

    override def ensureNoLocalRefs(block: Block, pt: Type, forcedDefined: Boolean = false)(implicit ctx: Context): Tree =
      block // optimization, no checking needed, as block symbols do not change.

    override def typedDefDef(ddef: untpd.DefDef, sym: Symbol)(implicit ctx: Context) = {
      val tpt1 = // keep UnitTypes intact in result position
        if (ddef.tpt.typeOpt isRef defn.UnitClass) untpd.TypeTree(defn.UnitType) withPos ddef.tpt.pos
        else ddef.tpt
      val ddef1 = untpd.cpy.DefDef(ddef, ddef.mods, ddef.name, Nil, ddef.vparamss, tpt1, ddef.rhs)
      super.typedDefDef(ddef1, sym)
    }

    override def typedTypeDef(tdef: untpd.TypeDef, sym: Symbol)(implicit ctx: Context) =
      EmptyTree

     /*
    override def transformStats(stats: List[Tree], exprOwner: Symbol)(implicit ctx: Context) = {
      val stats1 = super.transform(stats, exprOwner)
      if (ctx.owner.isClass) addBridges(stats1) else stats1
    }
    def addBridges(stats1: List[tpd.Tree])  = stats1
/*
     class ComputeBridges(unit: CompilationUnit, root: Symbol)(implicit  ctx:Context) {

       var toBeRemoved  = Set[Symbol]()
       val site         = root.thisType
       val bridgesScope = Scopes.newScope
       val bridgeTarget = scala.collection.mutable.HashMap[Symbol, Symbol]()
       var bridges      = List[Tree]()

       val opc = enteringExplicitOuter {
         new overridingPairs.Cursor(root) {
           override def parents              = List(root.info.firstParent)
           override def exclude(sym: Symbol) = !sym.isMethod || super.exclude(sym)
         }
       }

       def compute(): (List[Tree], scala.collection.immutable.Set[Symbol]) = {
         while (opc.hasNext) {
           if (enteringExplicitOuter(!opc.low.isDeferred))
             checkPair(opc.currentPair)

           opc.next()
         }
         (bridges, toBeRemoved)
       }

       /** Check that a bridge only overrides members that are also overridden by the original member.
         *  This test is necessary only for members that have a value class in their type.
         *  Such members are special because their types after erasure and after post-erasure differ/.
         *  This means we generate them after erasure, but the post-erasure transform might introduce
         *  a name clash. The present method guards against these name clashes.
         *
         *  @param  member   The original member
         *  @param  other    The overidden symbol for which the bridge was generated
         *  @param  bridge   The bridge
*/
       def checkBridgeOverrides(member: Symbol, other: Symbol, bridge: Symbol): Seq[(Position, String)] = {
         def fulldef(sym: Symbol) =
           if (sym == NoSymbol) sym.toString
           else s"$sym: ${sym.tpe} in ${sym.owner}"
         var noclash = true
         val clashErrors = mutable.Buffer[(Position, String)]()
         def clashError(what: String) = {
           val pos = if (member.owner == root) member.pos else root.pos
           val msg = sm"""bridge generated for member ${fulldef(member)}
                      |which overrides ${fulldef(other)}
                      |clashes with definition of $what;
                      |both have erased type ${exitingPostErasure(bridge.tpe)}"""
           clashErrors += Tuple2(pos, msg)
         }
         for (bc <- root.baseClasses) {
           if (settings.debug)
             exitingPostErasure(println(
               sm"""check bridge overrides in $bc
                |${bc.info.nonPrivateDecl(bridge.name)}
                |${site.memberType(bridge)}
                |${site.memberType(bc.info.nonPrivateDecl(bridge.name) orElse IntClass)}
                |${(bridge.matchingSymbol(bc, site))}"""))

           def overriddenBy(sym: Symbol) =
             sym.matchingSymbol(bc, site).alternatives filter (sym => !sym.isBridge)
           for (overBridge <- exitingPostErasure(overriddenBy(bridge))) {
             if (overBridge == member) {
               clashError("the member itself")
             } else {
               val overMembers = overriddenBy(member)
               if (!overMembers.exists(overMember =>
                 exitingPostErasure(overMember.tpe =:= overBridge.tpe))) {
                 clashError(fulldef(overBridge))
               }
             }
           }
         }
         clashErrors
       }

       /** TODO - work through this logic with a fine-toothed comb, incorporating
         *  into SymbolPairs where appropriate.
         */
       def checkPair(pair: SymbolPair) {
         import pair._
         val member = low
         val other  = high
         val otpe   = highErased

         val bridgeNeeded = exitingErasure (
           !member.isMacro &&
             !(other.tpe =:= member.tpe) &&
             !(deconstMap(other.tpe) =:= deconstMap(member.tpe)) &&
             { var e = bridgesScope.lookupEntry(member.name)
               while ((e ne null) && !((e.sym.tpe =:= otpe) && (bridgeTarget(e.sym) == member)))
                 e = bridgesScope.lookupNextEntry(e)
               (e eq null)
             }
         )
         if (!bridgeNeeded)
           return

         val newFlags = (member.flags | BRIDGE | ARTIFACT) & ~(ACCESSOR | DEFERRED | LAZY | lateDEFERRED)
         val bridge   = other.cloneSymbolImpl(root, newFlags) setPos root.pos

         debuglog("generating bridge from %s (%s): %s to %s: %s".format(
           other, flagsToString(newFlags),
           otpe + other.locationString, member,
           specialErasure(root)(member.tpe) + member.locationString)
         )

         // the parameter symbols need to have the new owner
         bridge setInfo (otpe cloneInfo bridge)
         bridgeTarget(bridge) = member

         def sigContainsValueClass = (member.tpe exists (_.typeSymbol.isDerivedValueClass))

         val shouldAdd = (
           !sigContainsValueClass
             ||  (checkBridgeOverrides(member, other, bridge) match {
             case Nil => true
             case es if member.owner.isAnonymousClass => resolveAnonymousBridgeClash(member, bridge); true
             case es => for ((pos, msg) <- es) unit.error(pos, msg); false
           })
           )

         if (shouldAdd) {
           exitingErasure(root.info.decls enter bridge)
           if (other.owner == root) {
             exitingErasure(root.info.decls.unlink(other))
             toBeRemoved += other
           }

           bridgesScope enter bridge
           bridges ::= makeBridgeDefDef(bridge, member, other)
         }
       }

       def makeBridgeDefDef(bridge: Symbol, member: Symbol, other: Symbol) = exitingErasure {
         // type checking ensures we can safely call `other`, but unless `member.tpe <:< other.tpe`,
         // calling `member` is not guaranteed to succeed in general, there's
         // nothing we can do about this, except for an unapply: when this subtype test fails,
         // return None without calling `member`
         //
         // TODO: should we do this for user-defined unapplies as well?
         // does the first argument list have exactly one argument -- for user-defined unapplies we can't be sure
         def maybeWrap(bridgingCall: Tree): Tree = {
           val guardExtractor = ( // can't statically know which member is going to be selected, so don't let this depend on member.isSynthetic
             (member.name == nme.unapply || member.name == nme.unapplySeq)
               && !exitingErasure((member.tpe <:< other.tpe))) // no static guarantees (TODO: is the subtype test ever true?)

           import CODE._
           val _false    = FALSE
           val pt        = member.tpe.resultType
           lazy val zero =
             if      (_false.tpe <:< pt)    _false
             else if (NoneModule.tpe <:< pt) REF(NoneModule)
             else EmptyTree

           if (guardExtractor && (zero ne EmptyTree)) {
             val typeTest = gen.mkIsInstanceOf(REF(bridge.firstParam), member.tpe.params.head.tpe)
             IF (typeTest) THEN bridgingCall ELSE zero
           } else bridgingCall
         }
         val rhs = member.tpe match {
           case MethodType(Nil, ConstantType(c)) => Literal(c)
           case _                                =>
             val sel: Tree    = Select(This(root), member)
             val bridgingCall = (sel /: bridge.paramss)((fun, vparams) => Apply(fun, vparams map Ident))

             maybeWrap(bridgingCall)
         }
         DefDef(bridge, rhs)
       }
     }*/

    override def typedNamed(tree: untpd.NameTree, pt: Type)(implicit ctx: Context): Tree = {
      if (tree eq untpd.EmptyValDef) return tpd.EmptyValDef
      assert(tree.hasType, tree)
      val sym = tree.symbol
      assert(sym.exists, tree)
      def localContext = ctx.fresh.setTree(tree).setOwner(sym)
      tree match {
        case tree: untpd.Ident => typedIdent(tree, pt)
        case tree: untpd.Select => typedSelect(tree, pt)
        case tree: untpd.ValDef => typedValDef(tree, sym)(localContext)
        case tree: untpd.DefDef => typedDefDef(tree, sym)(localContext)
        case tree: untpd.TypeDef =>
          if (tree.isClassDef) typedClassDef(tree, sym.asClass)(localContext)
          else EmptyTree
      }
    }

    override def adapt(tree: Tree, pt: Type)(implicit ctx: Context): Tree =
      ctx.traceIndented(i"adapting ${tree.showSummary}: ${tree.tpe} to $pt", show = true) {
        assert(ctx.phase == ctx.erasurePhase.next, ctx.phase)
        if (tree.isEmpty) tree else adaptToType(tree, pt)
    }
  }
}