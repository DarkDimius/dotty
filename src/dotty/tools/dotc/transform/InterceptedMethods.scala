package dotty.tools.dotc
package transform

import TreeTransforms._
import core.DenotTransformers._
import core.Denotations._
import core.SymDenotations._
import core.Contexts._
import core.Types._
import ast.Trees._
import ast.tpd.{Apply, Tree, cpy}
import dotty.tools.dotc.ast.tpd
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
import dotty.runtime.LazyVals
import scala.collection.mutable.ListBuffer
import dotty.tools.dotc.core.Denotations.SingleDenotation
import dotty.tools.dotc.core.SymDenotations.SymDenotation
import dotty.tools.dotc.core.DenotTransformers.DenotTransformer
import StdNames._

/** Replace member references as follows:
  *
  * - `x == y` for == in class Any becomes `x equals y` with equals in class Object.
  * - `x != y` for != in class Any becomes `!(x equals y)` with equals in class Object.
  * - `x.##` for ## in other classes becomes calls to ScalaRunTime.hash,
  *     using the most precise overload available
  * - `x.getClass` for getClass in primitives becomes `x.getClass` with getClass in class Object.
  * - `x.isInstanceOf[O]` if O is object becomes `x eq O` (reference equality)
  */
class InterceptedMethods extends TreeTransform {

  import tpd._

  override def name: String = "intercepted"

  // this should be removed if we have guarantee that ## will get Apply node
  override def transformSelect(tree: tpd.Select)(implicit ctx: Context, info: TransformerInfo): Tree = {
    if (tree.symbol.isTerm && defn.poundPoundMethods(tree.symbol.asTerm)) {
      val rewrite = PoundPoundValue(tree.qualifier)
      ctx.log(s"$name rewrote $tree to $rewrite")
      rewrite
    }
    else tree
  }

  private def PoundPoundValue(tree: Tree)(implicit ctx: Context) = {
    val s = tree.tpe.widen.typeSymbol
    if (s == defn.NullClass) Literal(Constant(0))
    else {
      // Since we are past typer, we need to avoid creating trees carrying
      // overloaded types.  This logic is custom (and technically incomplete,
      // although serviceable) for def hash.  What is really needed is for
      // the overloading logic presently hidden away in a few different
      // places to be properly exposed so we can just call "resolveOverload"
      // after typer.  Until then:
      def alts = defn.ScalaRuntimeModule.info.member(nme.hash_).alternatives
      def alt1 = alts find (_.info.firstParamTypes.head =:= tree.tpe)
      def alt2 = defn.ScalaRuntimeModule.info.member(nme.hash_)
        .suchThat (_.info.firstParamTypes.head.typeSymbol == defn.AnyClass)

      tpd.Apply(Ident(alt1.getOrElse(alt2).termRef), List(tree))
    }
  }

  override def transformApply(tree: Apply)(implicit ctx: Context, info: TransformerInfo): Tree = {
    def unknown = {
      ctx.debugwarn(s"The symbol '${tree.fun.symbol}' was interecepted but didn't match any cases, " +
        s"that means the intercepted methods set doesn't match the code")
      tree
    }
    if (tree.fun.symbol.isTerm && tree.args.isEmpty &&
        (defn.interceptedMethods contains tree.fun.symbol.asTerm)) {
      val rewrite: Tree = tree.fun match {
        case Select(qual, name) =>
          if (defn.poundPoundMethods contains tree.fun.symbol.asTerm) {
            PoundPoundValue(qual)
          } else if (defn.Any_comparisons contains tree.fun.symbol.asTerm) {
            if (tree.fun.symbol eq defn.Any_==) {
              Apply(Select(qual, defn.Object_equals.termRef), tree.args)
            } else if (tree.fun.symbol eq defn.Any_!=) {
              Select(Apply(Select(qual, defn.Object_equals.termRef), tree.args), defn.Boolean_!.termRef)
            } else unknown
          } /* else if (isPrimitiveValueClass(qual.tpe.typeSymbol)) {
            // todo: this is needed to support value classes
            // Rewrite 5.getClass to ScalaRunTime.anyValClass(5)
            global.typer.typed(gen.mkRuntimeCall(nme.anyValClass,
              List(qual, typer.resolveClassTag(tree.pos, qual.tpe.widen))))
          }*/
          else if (defn.primitiveGetClassMethods.contains(tree.fun.symbol)) {
            // if we got here then we're trying to send a primitive getClass method to either
            // a) an Any, in which cage Object_getClass works because Any erases to object. Or
            //
            // b) a non-primitive, e.g. because the qualifier's type is a refinement type where one parent
            //    of the refinement is a primitive and another is AnyRef. In that case
            //    we get a primitive form of _getClass trying to target a boxed value
            //    so we need replace that method name with Object_getClass to get correct behavior.
            //    See SI-5568.
            Apply(Select(qual, defn.Object_getClass.termRef), Nil)
          } else {
            unknown
          }
        case _ =>
          unknown
      }
      ctx.log(s"$name rewrote $tree to $rewrite")
      rewrite
    }
    else tree
  }
}
