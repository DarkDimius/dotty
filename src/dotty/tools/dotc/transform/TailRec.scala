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

/**
 * A Tail Rec Transformer
 *
 * @author     Erik Stenman, Iulian Dragos
 * ported to dotty by Dmitry Petrashko
 * @version    1.1
 *
 *             What it does:
 *             <p>
 *             Finds method calls in tail-position and replaces them with jumps.
 *             A call is in a tail-position if it is the last instruction to be
 *             executed in the body of a method.  This is done by recursing over
 *             the trees that may contain calls in tail-position (trees that can't
 *             contain such calls are not transformed). However, they are not that
 *             many.
 *             </p>
 *             <p>
 *             Self-recursive calls in tail-position are replaced by jumps to a
 *             label at the beginning of the method. As the JVM provides no way to
 *             jump from a method to another one, non-recursive calls in
 *             tail-position are not optimized.
 *             </p>
 *             <p>
 *             A method call is self-recursive if it calls the current method and
 *             the method is final (otherwise, it could
 *             be a call to an overridden method in a subclass).
 *
 *             Recursive calls on a different instance
 *             are optimized. Since 'this' is not a local variable it s added as
 *             a label parameter.
 *             </p>
 *             <p>
 *             This phase has been moved before pattern matching to catch more
 *             of the common cases of tail recursive functions. This means that
 *             more cases should be taken into account (like nested function, and
 *             pattern cases).
 *             </p>
 *             <p>
 *             If a method contains self-recursive calls, a label is added to at
 *             the beginning of its body and the calls are replaced by jumps to
 *             that label.
 *             </p>
 *             <p>
 *
 *             In scalac, If the method had type parameters, the call must contain same
 *             parameters as type arguments. This is no longer case in dotc.
 *             In scalac, this is named tailCall but it does only provide optimization for
 *             self recursive functions, that's why it's renamed to tailrec
 *             </p>
 */
class TailRec extends TreeTransform {

  import tpd._


  override def name: String = "tailrec"

  /** perform context-dependant initialization */
  override def init(implicit ctx: Context, info: TransformerInfo): Unit = {
  }

  private def mkLabel(method: Symbol, tp:Type)(implicit c: Context): TermSymbol = {
    val name = c.freshName("tailLabel")

    c.newSymbol(method, name.toTermName, Flags.Synthetic, tp)
  }

  // if Mandatory && !final fail("it is neither private nor final so can be overridden")

  override def transformDefDef(tree: tpd.DefDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    tree match {
      case dd@DefDef(_, name, _, vparamss0, _, rhs0) if (dd.symbol is Flags.Final) && !((dd.symbol is Flags.Accessor) || (rhs0 eq EmptyTree)) =>

        deriveDefDef(tree) { rhs =>
            val owner = ctx.owner.enclClass

            val newType: Type = dd.tpe.widen match {
              case t:PolyType => PolyType(t.paramNames)( x =>t.paramBounds,
                x =>MethodType(List("this".toTermName), List(owner.namedType), t.resultType))
              case t => MethodType(List("this".toTermName), List(owner.namedType), t)
            }

            val label = mkLabel(dd.symbol, newType)
            var rewrote = false

            // Note: in case speedup will be needed, t
            // his can be split in two separate transforms(in different groups),
            // than first one will collect info about which transformations and rewritings should be applied
            // and second one will actually apply them
            val res = tpd.Closure(label, args => {
              val thiz = args.head.head
              val argMapping: Map[Symbol, Tree] = ((vparamss0.flatten.map(_.symbol)) zip (args.tail.flatten)).toMap
              val claz = dd.symbol.enclClass
              val transformer = new TailCallElimination(thiz, argMapping, claz)(ctx)
              val c = new transformer.DefDefTailContext(dd, label)
              val rhs = transformer.transform(rhs0, c)
              rewrote = transformer.rewrote
              rhs
            })
            if (rewrote) res else rhs
            res
        }
      case d: DefDef if d.symbol.hasAnnotation(defn.TailrecClass) && !(d.symbol is Flags.Final) =>
        ctx.error("TailRec optimisation no applicable, method is neither private nor final so can be overridden", d.pos)
        d
      case _ => tree
    }

  }


  class TailCallElimination(val thiz: Tree, val argMapping: Map[Symbol, Tree], enclosingClass: ClassSymbol)(implicit val c: Context) extends tpd.TreeMap {

    import tpd._


    var rewrote = false

    private val defaultReason = "it contains a recursive call not in tail position"

    /** Has the label been accessed? Then its symbol is in this set. */
    def tailrecFailure(failReason: String, failPos:Position)(implicit c: Context) {
      val method = ctx.method

      c.error(s"could not optimize @tailrec annotated $method: $failReason", failPos)
    }

    // `accessed` was stored as boolean in the current context -- this is no longer tenable
    // with jumps to labels in tailpositions now considered in tailposition,
    // a downstream context may access the label, and the upstream one will be none the wiser
    // this is necessary because tail-calls may occur in places where syntactically they seem impossible
    // (since we now consider jumps to labels that are in tailposition, such as matchEnd(x) {x})

    sealed trait TailContext {
      // current method
      def method: Symbol

      def tparams: List[Symbol]

      // context is in tail position
      def tailPos: Boolean

      // new label, tail call target
      def label: Symbol

      def isMandatory = method.hasAnnotation(defn.TailrecClass)

      override def toString = s"${method.name} tparams=$tparams tailPos=$tailPos label=$label label info=${label.info}"
    }

    object EmptyTailContext extends TailContext {
      def method = NoSymbol
      def tparams = Nil
      def methodPos = NoPosition
      def tailPos = false
      def label = NoSymbol
    }

    class DefDefTailContext(dd: DefDef, var label: TermSymbol) extends TailContext {
      def method = dd.symbol
      def tparams = dd.tparams map (_.symbol)
      def methodPos = dd.pos
      def tailPos = true

      private def isRecursiveCall(t: Tree) = {
        val receiver = t.symbol

        ((receiver != null)
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
      def method = that.method
      def tparams = that.tparams
      def label = that.label
    }

    private var ctx: TailContext = EmptyTailContext
    private def noTailContext() = new ClonedTailContext(ctx, tailPos = false)
    private def yesTailContext() = new ClonedTailContext(ctx, tailPos = true)

    /** Rewrite this tree to contain no tail recursive calls */
    def transform(tree: Tree, nctx: TailContext): Tree = {
      val saved = ctx
      ctx = nctx
      try transform(tree)
      finally this.ctx = saved
    }

    def yesTailTransform(tree: Tree): Tree =
      if (!ctx.tailPos) transform(tree, yesTailContext())
      else transform(tree)
    def noTailTransform(tree: Tree): Tree =
      if (ctx.tailPos) transform(tree, noTailContext())
      else transform(tree)

    def noTailTransforms(trees: List[Tree]) = {
      val nctx = noTailContext()
      trees map (t => transform(t, nctx))
    }

    override def transform(tree: Tree)(implicit c: Context): Tree = {
      /* A possibly polymorphic apply to be considered for tail call transformation. */
      def rewriteApply(target: Tree, fun: Tree, targs: List[Tree], args: List[Tree]): Tree = {
        val receiver: Tree = fun match {
          case Select(qual, _) => qual
          case _ => EmptyTree // todo: ???
        }
        def receiverIsSame = enclosingClass.typeRef.widen =:= receiver.tpe.widen
        def receiverIsSuper = enclosingClass.typeRef.widen <:< receiver.tpe.widen
        def isRecursiveCall = (ctx.method eq fun.symbol) && ctx.tailPos
        def transformArgs = noTailTransforms(args)
        def matchesTypeArgs = ctx.tparams sameElements (targs map (_.tpe.typeSymbol))

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
          rewrote = true
          val method = if(targs.nonEmpty) TypeApply(Ident(ctx.label.termRef), targs) else Ident(ctx.label.termRef)
          Apply(Apply(method, List(noTailTransform(recv))), transformArgs)
        }

        if (!isRecursiveCall) {
          if (receiverIsSuper) failHere("it contains a recursive call targeting a supertype")
          else failHere(defaultReason)
        } else if (!matchesTypeArgs) failHere("it is called recursively with different type arguments")
        else if (receiver eq EmptyTree) rewriteTailCall(thiz)
        else if (!receiverIsSame) failHere("it changes type of 'this' on a polymorphic recursive call")
        else rewriteTailCall(receiver)
      }

      val res: Tree = tree match {
        case ValDef(_, _, _, _) =>
          if ((tree.symbol is Lazy) && tree.symbol.hasAnnotation(defn.TailrecClass))
            c.error("lazy vals are not tailcall transformed", tree.pos)
          super.transform(tree)

        case t: DefDef =>
          t
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
            transformSub(cases)
          )

        case Try(block, catches, finalizer@EmptyTree) =>
          // SI-1672 Catches are in tail position when there is no finalizer
          tpd.cpy.Try(tree,
            noTailTransform(block),
            transform(catches),
            EmptyTree
          )

        case Try(block, catches, finalizer) =>
          // no calls inside a try are in tail position if there is a finalizer, but keep recursing for assertions
          tpd.cpy.Try(tree,
            noTailTransform(block),
            noTailTransform(catches),
            noTailTransform(finalizer)
          )

        case Apply(tapply@TypeApply(fun, targs), vargs) =>
          rewriteApply(tapply, fun, targs, vargs)

        case Apply(fun, args) if fun.symbol == defn.Boolean_or || fun.symbol == defn.Boolean_and =>
          tpd.cpy.Apply(tree, fun, transform(args))

        case Apply(fun, args) =>
          rewriteApply(fun, fun, Nil, args)
        case Alternative(_) | Bind(_, _) =>
          assert(false, "We should've never gotten inside a pattern")
          tree
        case Select(qual, name) =>
          tpd.cpy.Select(tree, noTailTransform(qual), name)
        case EmptyTree | Super(_, _) | This(_) | Literal(_) | TypeTree(_)| DefDef(_, _, _, _, _, _)| TypeDef(_, _, _) =>
          tree
        case Ident(qual) =>
          argMapping.get(tree.symbol) match {
            case Some(rewrite) => rewrite
            case None => tree.tpe match {
              case TermRef(ThisType(enclosingClass), qual) =>
                Select(thiz, qual)
              case _ => tree
            }
          }
        case _ =>
          super.transform(tree)
      }

      if (ctx.isMandatory) res match {
        case Apply(fn, _) if (fn.symbol == ctx.method) =>
          tailrecFailure(defaultReason, res.pos)
      }
      res
    }
 }
}

