package dotty.tools.dotc
package transform

import core._
import Contexts._, Symbols._, Types._, Flags._, Decorators._, StdNames._, Constants._, Phases._
import TreeTransforms._
import ast.Trees._
import dotty.tools.dotc.ast.{TreeTypeMap, tpd}
import dotty.tools.dotc.core.DenotTransformers.{DenotTransformer, InfoTransformer}
import dotty.tools.dotc.core.Denotations.SingleDenotation
import dotty.tools.dotc.core.Names.{TermName, Name}
import dotty.tools.dotc.core.SymDenotations.SymDenotation
import collection.mutable

class Optional extends MiniPhaseTransform with DenotTransformer {
  thisTransformer =>

  import tpd._
  import Optional._

  def phaseName: String = "Optional"

  private val newMappings = mutable.HashMap[Symbol, (Symbol, Symbol)]()
  private val newDefs = mutable.HashMap[Symbol, Symbol]()


  override def checkPostCondition(tree: tpd.Tree)(implicit ctx: Context): Unit = {
    val sym = tree.symbol
    if (sym.exists && sym.owner.exists && sym.info.paramTypess.exists(_.exists(x => x.derivesFrom(OptionalClaz)))) {
      assert(sym.owner.asClass.classInfo.decl(sym.name ++ "$unboxed").exists)
    }
  }

  private def duplicateIfNeeded(sym: Symbol)(implicit ctx: Context): Symbol = {
    def candidate = sym.info.paramTypess.exists(_.exists(x => x.derivesFrom(OptionalClaz)))
    if (sym.is(Flags.Method) && candidate) {

      def splitOption(n: TermName, t: Type): List[(TermName, Type)] = t match {
        case a@Optional(underlying) =>
          List((n ++ "_f".toTermName, defn.BooleanType), (n ++ "_u".toTermName, underlying))
        case _ => (n, t) :: Nil
      }

      def splitOptions(tp: Type): Type = tp match {
        case t: MethodType =>
          val (paramNames, paramTypes) = (t.paramNames zip t.paramTypes).flatMap(x => splitOption(x._1, x._2)).unzip
          t.derivedMethodType(paramNames, paramTypes, splitOptions(t.resultType))
        case t: PolyType =>
          t.duplicate(resType = splitOptions(t.resultType))
        case _ => tp
      }

      val r = ctx.newSymbol(sym.owner, sym.name.asTermName ++ "$unboxed", sym.flags | Flags.Synthetic,
        splitOptions(sym.info.widen), sym.privateWithin, sym.coord)
      newDefs(sym) = r
      r
    } else NoSymbol
  }


  /** The transformation method */
  def transform(ref: SingleDenotation)(implicit ctx: Context): SingleDenotation = {
    ref match {
      case t: SymDenotation if t.isClass && !t.is(Package) =>
        val newDecls = t.asClass.unforcedDecls.flatMap { x => val s = duplicateIfNeeded(x); if (s.exists) s :: Nil else Nil }
        val oldClassInfo = t.asClass.classInfo
        val newScope = oldClassInfo.decls.cloneScope
        newDecls.foreach(newScope.enter)
        t.copySymDenotation(info = oldClassInfo.derivedClassInfo(decls = newScope))
      case _ =>
        ref
    }
  }

  override def transformValDef(tree: tpd.ValDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree =
    if (tree.tpe.derivesFrom(OptionalClaz) && !ctx.owner.isClass
      && (isIdempotent(tree.rhs) || (tree.rhs.symbol eq SomeApply))
      && !tree.symbol.is(Param)) {

      val f = tpd.SyntheticValDef(tree.name ++ "_f".toTermName, transformSelect(tree.rhs.select("isEmpty".toTermName)))
      val u = tpd.SyntheticValDef(tree.name ++ "_u".toTermName, transformSelect(tree.rhs.select("underlying".toTermName)))
      newMappings(tree.symbol) = (f.symbol, u.symbol)
      Thicket(f, u)
    } else tree

  def transformRef(tree: tpd.RefTree)(implicit ctx: Context, info: TransformerInfo): tpd.Tree =
    newMappings.get(tree.symbol) match {
      case Some((f, u)) =>
        ref(OptionalModule).select(nme.apply).appliedToType(u.info.widen).appliedTo(ref(f), ref(u))
      case _ =>
        tree
    }

  override def transformSelect(tree: tpd.Select)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = transformRef(tree)

  override def transformIdent(tree: tpd.Ident)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = transformRef(tree)

  override def transformDefDef(tree: tpd.DefDef)(implicit ctx: Context, info: TransformerInfo): tpd.Tree = {
    if (tree.vparamss.exists(_.exists(x => x.tpe.derivesFrom(OptionalClaz)))) {
      val origSym = tree.symbol
      val origArgSyms = tree.vparamss.flatMap(_.map(_.symbol))
      val newSymbol = newDefs.getOrElse(origSym, duplicateIfNeeded(origSym)).asTerm
      val newDef = tpd.polyDefDef(newSymbol, targs => args => {
        val newArgs = args.flatMap(_.map(_.symbol)).iterator
        val mapping: Map[Symbol, (Symbol, Symbol, Type)] = origArgSyms.map { x => x.info match {
          case Optional(underlying) => x ->(newArgs.next(), newArgs.next(), underlying)
          case _ => x ->(newArgs.next(), NoSymbol, NoType)
        }
        }.toMap

        val refMap: Tree => Tree = {
          case t: RefTree => mapping.get(t.symbol) match {
            case Some((a, NoSymbol, NoType)) => ref(a)
            case Some((f, u, underlying)) =>
              ref(OptionalModule).select(nme.apply).appliedToType(underlying).appliedTo(ref(f), ref(u))
            case None => t
          }
          case t => t
        }

        assert(newArgs.isEmpty)
        val newDef = new TreeTypeMap(oldOwners = List(origSym), newOwners = List(newSymbol), treeMap = refMap).apply(tree.rhs)
        newDef
      })

      val fwd = cpy.DefDef(tree)(
          rhs = transformApply(ref(origSym).appliedToTypes(tree.tparams.map(_.symbol.typeRef)).
            appliedToArgss(tree.vparamss.nestedMap(vparam => ref(vparam.symbol))).asInstanceOf[Apply]))

      Thicket(fwd, newDef)
    } else tree
  }

  override def transformApply(tree: tpd.Apply)(implicit ctx: Context, info: TransformerInfo): tpd.Tree =
    newDefs.get(tree.fun.symbol) match {
      case Some(x) if tree.args.filter(_.tpe.derivesFrom(OptionalClaz)).forall(isIdempotent) =>
        val rec: Tree = tree.fun match {
          case Select(qual, _) => qual
          case t => t.tpe match {
            case TermRef(prefix: NamedType, _) =>
              ref(prefix)
          }
        }
        rec.select(x).appliedToArgs(
          tree.args.flatMap(x => if (x.tpe.derivesFrom(OptionalClaz)) {
            x.select("isEmpty".toTermName) :: x.select("underlying".toTermName) :: Nil
          } else x :: Nil))
      case _ => tree
    }
}

object Optional {
  def OptionalClaz(implicit ctx: Context): ClassSymbol = ctx.requiredClass("dotty.Optional")
  def OptionalModule(implicit ctx: Context): Symbol = ctx.requiredModule("dotty.Optional")
  def NoneModule(implicit ctx: Context): Symbol = ctx.requiredModule("dotty.None")
  def SomeModule(implicit ctx: Context): Symbol = ctx.requiredModule("dotty.Some")
  def OptionalApply(implicit ctx: Context): Symbol = OptionalModule.requiredMethod("apply")
  def SomeApply(implicit ctx: Context): Symbol = SomeModule.requiredMethod("apply")


  def isIdempotent(tree: tpd.Tree)(implicit ctx: Context): Boolean = {
    tpd.isIdempotentExpr(tree) || (tree.symbol eq SomeApply) || (tree.symbol eq OptionalApply)
  }

  def apply(elem: Type)(implicit ctx: Context) =
    if (ctx.erasedTypes) OptionalClaz.typeRef
    else OptionalClaz.typeRef.appliedTo(elem :: Nil)
  def unapply(tp: Type)(implicit ctx: Context): Option[Type] = tp.dealias match {
    case at: RefinedType if (at isRef OptionalClaz) && at.argInfos.length == 1 => Some(at.argInfos.head)
    case _ => None
  }
}

