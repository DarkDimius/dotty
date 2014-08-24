package dotty.tools
package dotc
package ast

import core._
import Types._, Contexts._, Constants._, Names._, Flags._
import SymDenotations._, Symbols._, Annotations._, Trees._, Symbols._
import Denotations._, Decorators._

/** A map that applies three functions and a substitution together to a tree and
 *  makes sure they are coordinated so that the result is well-typed. The functions are
 *  @param  typeMap  A function from Type to Type that gets applied to the
 *                   type of every tree node and to all locally defined symbols,
 *                   followed by the substitution [substFrom := substTo].
 *  @param ownerMap  A function that translates owners of top-level local symbols
 *                   defined in the mapped tree.
 *  @param treeMap   A transformer that translates all encountered subtrees in
 *                   prefix traversal order.
 *  @param substFrom The symbols that need to be substituted
 *  @param substTo   The substitution targets
 *
 *  The reason the substitution is broken out from the rest of the type map is
 *  that all symbols have to be substituted at the same time. If we do not do this,
 *  we risk data races on named types. Example: Say we have `outer#1.inner#2` and we
 *  have two substitutons S1 = [outer#1 := outer#3], S2 = [inner#2 := inner#4] where
 *  hashtags precede symbol ids. If we do S1 first, we get outer#2.inner#3. If we then
 *  do S2 we get outer#2.inner#4. But that means that the named type outer#2.inner
 *  gets two different denotations in the same period. Hence, if -YnoDoubleBindings is
 *  set, we would get a data race assertion error.
 */
final class TreeTypeMap(
  val typeMap: Type => Type = IdentityTypeMap,
  val ownerMap: Symbol => Symbol = identity _,
  val treeMap: tpd.Tree => tpd.Tree = identity _,
  val substFrom: List[Symbol] = Nil,
  val substTo: List[Symbol] = Nil)(implicit ctx: Context) extends tpd.TreeMap {
  import tpd._

  def mapType(tp: Type) = typeMap(tp).substSym(substFrom, substTo)

  override def transform(tree: tpd.Tree)(implicit ctx: Context): tpd.Tree = treeMap(tree) match {
    case impl @ Template(constr, parents, self, body) =>
      val tmap = withMappedSyms(impl.symbol :: impl.constr.symbol :: Nil)
      val constr1 = tmap.transformSub(constr)
      val parents1 = parents mapconserve transform
      var self1 = transformDefs(self :: Nil)._2.head
      val body1 = tmap.transformStats(body)
      cpy.Template(impl)(constr1, parents1, self1, body1).withType(tmap.mapType(impl.tpe))
    case tree1 =>
      tree1.withType(mapType(tree1.tpe)) match {
        case id: Ident if tpd.needsSelect(id.tpe) =>
          ref(id.tpe.asInstanceOf[TermRef]).withPos(id.pos)
        case ddef @ DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
          val (tmap1, tparams1) = transformDefs(ddef.tparams)
          val (tmap2, vparamss1) = tmap1.transformVParamss(vparamss)
          cpy.DefDef(ddef)(mods, name, tparams1, vparamss1, tmap2.transform(tpt), tmap2.transform(rhs))
        case blk @ Block(stats, expr) =>
          val (tmap1, stats1) = transformDefs(stats)
          val expr1 = tmap1.transform(expr)
          cpy.Block(blk)(stats1, expr1)
        case cdef @ CaseDef(pat, guard, rhs) =>
          val tmap = withMappedSyms(patVars(pat))
          val pat1 = tmap.transform(pat)
          val guard1 = tmap.transform(guard)
          val rhs1 = tmap.transform(rhs)
          cpy.CaseDef(cdef)(pat1, guard1, rhs1)
        case tree1 =>
          super.transform(tree1)
      }
  }

  override def transformStats(trees: List[tpd.Tree])(implicit ctx: Context) =
    transformDefs(trees)._2

  private def transformDefs[TT <: tpd.Tree](trees: List[TT])(implicit ctx: Context): (TreeTypeMap, List[TT]) = {
    val tmap = withMappedSyms(tpd.localSyms(trees))
    (tmap, tmap.transformSub(trees))
  }

  private def transformVParamss(vparamss: List[List[ValDef]]): (TreeTypeMap, List[List[ValDef]]) = vparamss match {
    case vparams :: rest =>
      val (tmap1, vparams1) = transformDefs(vparams)
      val (tmap2, vparamss2) = tmap1.transformVParamss(rest)
      (tmap2, vparams1 :: vparamss2)
    case nil =>
      (this, vparamss)
  }

  def apply[ThisTree <: tpd.Tree](tree: ThisTree): ThisTree = transform(tree).asInstanceOf[ThisTree]

  def apply(annot: Annotation): Annotation = {
    val tree1 = apply(annot.tree)
    if (tree1 eq annot.tree) annot else ConcreteAnnotation(tree1)
  }

  /** The current tree map composed with a substitution [from -> to] */
  def withSubstitution(from: List[Symbol], to: List[Symbol]): TreeTypeMap =
    if (from eq to) this
    else {
      // assert that substitution stays idempotent, assuming its parts are
      assert(!from.exists(substTo contains _))
      assert(!to.exists(substFrom contains _))
      new TreeTypeMap(
        typeMap,
        ownerMap andThen { sym =>
          val idx = from.indexOf(sym)
          if (idx >= 0) to(idx) else sym
        },
        treeMap,
        from ++ substFrom,
        to ++ substTo)
    }

  /** Apply `typeMap` and `ownerMap` to given symbols `syms`
   *  and return a treemap that contains the substitution
   *  between original and mapped symbols.
   */
  def withMappedSyms(syms: List[Symbol]): TreeTypeMap = {
    val mapped = ctx.mapSymbols(syms, this)
    withSubstitution(syms, mapped)
  }
}