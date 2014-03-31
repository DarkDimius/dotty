package dotty.tools.dotc.transform

import dotty.tools.dotc.transform.TreeTransforms.{TransformerInfo, TreeTransform, TreeTransformer}
import dotty.tools.dotc.ast.{Trees, tpd}
import dotty.tools.dotc.core.Contexts.Context
import scala.collection.mutable.ListBuffer
import dotty.tools.dotc.core._
import dotty.tools.dotc.core.Symbols.NoSymbol
import scala.annotation.tailrec
import Types._, Contexts._, Constants._, Names._, NameOps._, Flags._
import SymDenotations._, Symbols._, StdNames._, Annotations._, Trees._
import Decorators._
import Symbols._
import scala.Some
import dotty.tools.dotc.transform.TreeTransforms.{NXTransformations, TransformerInfo, TreeTransform, TreeTransformer}
import dotty.tools.dotc.core.Contexts.Context
import scala.collection.mutable
import dotty.tools.dotc.core.Names.Name
import NameOps._
import dotty.tools.dotc.CompilationUnit
import dotty.tools.dotc.util.Positions.{Position, Coord}
import dotty.tools.dotc.util.Positions.NoPosition
import dotty.tools.dotc.ast.tpd.TreeAccumulator

/** A transformer that provides a convenient way to create companion objects
  */
abstract class TailRec(group: TreeTransformer, idx: Int) extends TreeTransform {

  import tpd._
  import tpd.TreeAccumulator

  override def transformDefDef(tree: tpd.DefDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {

    tree
  }
}




  /**
   * A Tail Call Transformer
   *
   * @author     Erik Stenman, Iulian Dragos
   * @version    1.1
   *
   * What it does:
   * <p>
   *   Finds method calls in tail-position and replaces them with jumps.
   *   A call is in a tail-position if it is the last instruction to be
   *   executed in the body of a method.  This is done by recursing over
   *   the trees that may contain calls in tail-position (trees that can't
   *   contain such calls are not transformed). However, they are not that
   *   many.
   * </p>
   * <p>
   *   Self-recursive calls in tail-position are replaced by jumps to a
   *   label at the beginning of the method. As the JVM provides no way to
   *   jump from a method to another one, non-recursive calls in
   *   tail-position are not optimized.
   * </p>
   * <p>
   *   A method call is self-recursive if it calls the current method and
   *   the method is final (otherwise, it could
   *   be a call to an overridden method in a subclass). Furthermore, If
   *   the method has type parameters, the call must contain these
   *   parameters as type arguments. Recursive calls on a different instance
   *   are optimized. Since 'this' is not a local variable, a dummy local val
   *   is added and used as a label parameter. The backend knows to load
   *   the corresponding argument in the 'this' (local at index 0). This dummy local
   *   is never used and should be cleand up by dead code elimination (when enabled).
   * </p>
   * <p>
   *   This phase has been moved before pattern matching to catch more
   *   of the common cases of tail recursive functions. This means that
   *   more cases should be taken into account (like nested function, and
   *   pattern cases).
   * </p>
   * <p>
   *   If a method contains self-recursive calls, a label is added to at
   *   the beginning of its body and the calls are replaced by jumps to
   *   that label.
   * </p>
   * <p>
   *   Assumes: `Uncurry` has been run already, and no multiple
   *            parameter lists exit.
   * </p>
   */
  class TailCallElimination(unit: CompilationUnit)(implicit c:Context) extends tpd.TreeMap {
    import tpd._
    private def defaultReason = "it contains a recursive call not in tail position"

    /** Has the label been accessed? Then its symbol is in this set. */
    private var accessed = Set[Symbol]()
    private val failPositions = mutable.HashMap[TailContext, Position]() withDefault (_.methodPos)
    private val failReasons   = mutable.HashMap[TailContext, String]() withDefaultValue defaultReason
    private def tailrecFailure(ctx: TailContext) {
      val method      = ctx.method
      val failReason  = failReasons(ctx)
      val failPos     = failPositions(ctx)

      c.error(s"could not optimize @tailrec annotated $method: $failReason", failPos)
    }
    // `accessed` was stored as boolean in the current context -- this is no longer tenable
    // with jumps to labels in tailpositions now considered in tailposition,
    // a downstream context may access the label, and the upstream one will be none the wiser
    // this is necessary because tail-calls may occur in places where syntactically they seem impossible
    // (since we now consider jumps to labels that are in tailposition, such as matchEnd(x) {x})

    sealed trait TailContext {
      def method: Symbol          // current method
      def tparams: List[Symbol]   // type parameters
      def methodPos: Position     // default position for failure reporting
      def tailPos: Boolean        // context is in tail position
      def label: Symbol           // new label, tail call target

      def enclosingType:Type = method.enclClass.typeRef
      def isEligible    = method.flags is Flags.Final
      def isMandatory   = method.hasAnnotation(defn.TailrecClass)
      def isTransformed = isEligible && accessed(label)

      def newThis(owner:Symbol) = {
        c.newSymbol(owner, nme.THIS, Flags.Synthetic, enclosingType)
      }
      override def toString = s"${method.name} tparams=$tparams tailPos=$tailPos label=$label label info=${label.info}"
    }

    object EmptyTailContext extends TailContext {
      def method     = NoSymbol
      def tparams    = Nil
      def methodPos  = NoPosition
      def tailPos    = false
      def label      = NoSymbol
    }

    class DefDefTailContext(dd: DefDef) extends TailContext {
      def method    = dd.symbol
      def tparams   = dd.tparams map (_.symbol)
      def methodPos = dd.pos
      def tailPos   = true

      lazy val label:TermSymbol      = mkLabel()

      private def mkLabel() = {
        val name = c.freshName("tailLabel")
        val origMethodType = method.info.asInstanceOf[MethodType]

        val tpe = MethodType(origMethodType.paramNames ++ List("thiz".toTermName),
          origMethodType.paramTypes ++ List(method.enclosingClass.typeRef), origMethodType.resultType)
        c.newSymbol(method, name.toTermName, Flags.Synthetic, tpe)
      }

      private def isRecursiveCall(t: Tree) = {
        val receiver = t.symbol

        (    (receiver != null)
          && receiver.isTerm // check if receiver is method?
          && (method.name == receiver.name)
          && (method.enclClass isSubClass receiver.enclClass)
        )
      }
      def containsRecursiveCall(t: Tree) = new TreeAccumulator[Boolean] {
        override def apply(x: Boolean, tree: tpd.Tree): Boolean = x || isRecursiveCall(tree)
      }.apply(false, t)
    }
    class ClonedTailContext(that: TailContext, override val tailPos: Boolean) extends TailContext {
      def method     = that.method
      def tparams    = that.tparams
      def methodPos  = that.methodPos
      def label      = that.label
    }

    private var ctx: TailContext = EmptyTailContext
    private def noTailContext()  = new ClonedTailContext(ctx, tailPos = false)
    private def yesTailContext() = new ClonedTailContext(ctx, tailPos = true)

    /** Rewrite this tree to contain no tail recursive calls */
    def transform(tree: Tree, nctx: TailContext): Tree = {
      val saved = ctx
      ctx = nctx
      try transform(tree)
      finally this.ctx = saved
    }

    def yesTailTransform(tree: Tree): Tree = transform(tree, yesTailContext())
    def noTailTransform(tree: Tree): Tree = transform(tree, noTailContext())
    def noTailTransforms(trees: List[Tree]) = {
      val nctx = noTailContext()
      trees map (t => transform(t, nctx))
    }

    override def transform(tree: Tree): Tree = {
      /* A possibly polymorphic apply to be considered for tail call transformation. */
      def rewriteApply(target: Tree, fun: Tree, targs: List[Tree], args: List[Tree]): Tree = {
        val receiver: Tree = fun match {
          case Select(qual, _)  => qual
          case _                => EmptyTree // todo: ???
        }
        def receiverIsSame    = ctx.enclosingType.widen =:= receiver.tpe.widen
        def receiverIsSuper   = ctx.enclosingType.widen <:< receiver.tpe.widen
        def isRecursiveCall   = (ctx.method eq fun.symbol) && ctx.tailPos
        def transformArgs     = noTailTransforms(args)
        def matchesTypeArgs   = ctx.tparams sameElements (targs map (_.tpe.typeSymbol))

        /* Records failure reason in Context for reporting.
         * Position is unchanged (by default, the method definition.)
         */
        def fail(reason: String) = {
          c.debuglog("Cannot rewrite recursive call at: " + fun.pos + " because: " + reason)
          tpd.cpy.Apply(tree, noTailTransform(target), transformArgs)
        }
        /* Position of failure is that of the tree being considered. */
        def failHere(reason: String) = {
          fail(reason)
        }
        def rewriteTailCall(recv: Tree): Tree = {
          c.debuglog("Rewriting tail recursive call:  " + fun.pos)
          accessed += ctx.label
            Apply(Ident(ctx.label.termRef), noTailTransform(recv) :: transformArgs)
          }


        if (!ctx.isEligible)            fail("it is neither private nor final so can be overridden")
        else if (!isRecursiveCall) {
          if (receiverIsSuper)          failHere("it contains a recursive call targeting a supertype")
          else                          failHere(defaultReason)
        }
        else if (!matchesTypeArgs)      failHere("it is called recursively with different type arguments")
        else if (receiver == EmptyTree) rewriteTailCall(Ident(fun.enclClass.termRef))
        else if (!receiverIsSame)       failHere("it changes type of 'this' on a polymorphic recursive call")
        else                            rewriteTailCall(receiver)
      }

      tree match {
        case ValDef(_, _, _, _) =>
          if ((tree.symbol is Lazy) && tree.symbol.hasAnnotation(defn.TailrecClass))
            c.error("lazy vals are not tailcall transformed", tree.pos)

          super.transform(tree)

        case dd @ DefDef(_, name, _, vparamss0, _, rhs0) if !(dd.symbol is Flags.Accessor) =>
          val newCtx = new DefDefTailContext(dd)
          if (newCtx.isMandatory && !(newCtx containsRecursiveCall rhs0))
            c.error("@tailrec annotated method contains no recursive calls", tree.pos)

          val newRHS = transform(rhs0, newCtx)

          deriveDefDef(tree) { rhs =>
            if (newCtx.isTransformed) {
              /* We have rewritten the tree, but there may be nested recursive calls remaining.
               * If @tailrec is given we need to fail those now.
               */
              if (newCtx.isMandatory) {
                for (t <- newRHS) //TODO: what it means
                  t match {
                    case Apply(fn, _) if (fn.symbol == newCtx.method) =>
                      t
                      failPositions(newCtx) = t
                      tailrecFailure(newCtx)
                    case _ =>
                  }
              }
              val newThis = newCtx.newThis(tree.symbol.owner)
              val vpSyms  = vparamss0.flatten map (_.symbol)

              tpd.Closure(ctx.label.asTerm, args => EmptyTree )
              /*Block(
                List(ValDef(newThis, This(tree.enclClass))),
                LabelDef(newCtx.label, newThis :: vpSyms, mkAttributedCastHack(newRHS, newCtx.label.tpe.resultType))
              ).addPos(tree.pos)*/
            }
            else {
              if (newCtx.isMandatory && newCtx.containsRecursiveCall(newRHS))
                tailrecFailure(newCtx)

              newRHS
            }
          }

        case Block(stats, expr) =>
          tpd.cpy.Block(tree,
            noTailTransforms(stats),
            transform(expr)
          )

        case CaseDef(pat, guard, body) =>
          deriveCaseDef(tree)(transform)

        case If(cond, thenp, elsep) =>
          tpd.cpy.If(tree,
            cond,
            transform(thenp),
            transform(elsep)
          )

        case Match(selector, cases) =>
          tpd.cpy.Match(tree,
            noTailTransform(selector),
            transformTrees(cases).asInstanceOf[List[CaseDef]]
          )

        case Try(block, catches, finalizer @ EmptyTree) =>
          // SI-1672 Catches are in tail position when there is no finalizer
          tpd.cpy.Try(tree,
            noTailTransform(block),
            transform(catches),
            EmptyTree
          )

        case Try(block, catches, finalizer) =>
           // no calls inside a try are in tail position if there is a finalizer, but keep recursing for nested functions
          tpd.cpy.Try(tree,
            noTailTransform(block),
            noTailTransform(catches),
            noTailTransform(finalizer)
          )

        case Apply(tapply @ TypeApply(fun, targs), vargs) =>
          rewriteApply(tapply, fun, targs, vargs)

        case Apply(fun, args) if fun.symbol == defn.Boolean_or || fun.symbol == defn.Boolean_and =>
          tpd.cpy.Apply(tree, fun, transformTrees(args))

        case Apply(fun, args) =>
          rewriteApply(fun, fun, Nil, args)
        case Alternative(_) | Bind(_, _) =>
          c.error("We should've never gotten inside a pattern")
          tree
        case Select(qual, name) =>
          tpd.cpy.Select(tree, noTailTransform(qual), name)
        case EmptyTree | Super(_, _) | This(_) | Ident(_) | Literal(_) |  TypeTree(_) =>
          tree
        case _ =>
          super.transform(tree)
      }
    }

    // Workaround for SI-6900. Uncurry installs an InfoTransformer and a tree Transformer.
    // These leave us with conflicting view on method signatures; the parameter symbols in
    // the MethodType can be clones of the ones originally found on the parameter ValDef, and
    // consequently appearing in the typechecked RHS of the method.
    private def mkAttributedCastHack(tree: Tree, tpe: Type) = ???
      ///gen.mkAttributedCast(tree, tpe)
    def transformTrees(trees: List[Tree]): List[Tree] =
        if (trees.isEmpty) Nil else trees mapConserve transform
  }

