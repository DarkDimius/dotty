package dotty.tools.dotc.transform

import dotty.tools.dotc.ast.tpd.TypedTreeCopier
import dotty.tools.dotc.ast.{untpd, tpd}
import dotty.tools.dotc.core.Types.Type
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.util.Attachment
import dotty.tools.dotc.core.Phases.Phase
import tpd.Tree
import dotty.tools.dotc.ast.Trees._
import scala.annotation.tailrec
import dotty.tools.dotc.core.Names.{TermName, TypeName, Name}
import dotty.tools.dotc.core.Constants.Constant

object TreeTransformation {
  val Finished = new Attachment.Key[TreeTransformerPhase]
}

abstract class TreeTransformation {

  import tpd._

  def transformIdent(tree: Ident, name: Name)(implicit ctx: Context): Tree = cpy.Ident(tree, name)

  def transformSelect(tree: Select, qualifier: Tree, name: Name)(implicit ctx: Context): Tree = cpy.Select(tree, qualifier, name)

  def transformThis(tree: This, qual: TypeName)(implicit ctx: Context): Tree = cpy.This(tree, qual)

  def transformSuper(tree: Super, qual: Tree, mix: TypeName)(implicit ctx: Context): Tree = cpy.Super(tree, qual, mix)

  def transformApply(tree: Apply, fun: Tree, args: List[Tree])(implicit ctx: Context): Tree = cpy.Apply(tree, fun, args)

  def transformTypeApply(tree: TypeApply, fun: Tree, args: List[Tree])(implicit ctx: Context): Tree = cpy.TypeApply(tree, fun, args)

  def transformLiteral(tree: Literal, const: Constant)(implicit ctx: Context): Tree = cpy.Literal(tree, const)

  def transformNew(tree: New, tpt: Tree)(implicit ctx: Context): Tree = cpy.New(tree, tpt)

  def transformPair(tree: Pair, left: Tree, right: Tree)(implicit ctx: Context): Tree = cpy.Pair(tree, left, right)

  def transformTyped(tree: Typed, expr: Tree, tpt: Tree)(implicit ctx: Context): Tree = cpy.Typed(tree, expr, tpt)

  def transformNamedArg(tree: NamedArg, name: Name, arg: Tree)(implicit ctx: Context): Tree = cpy.NamedArg(tree, name, arg)

  def transformAssign(tree: Assign, lhs: Tree, rhs: Tree)(implicit ctx: Context): Tree = cpy.Assign(tree, lhs, rhs)

  def transformBlock(tree: Block, stats: List[Tree], expr: Tree)(implicit ctx: Context): Tree = cpy.Block(tree, stats, expr)

  def transformIf(tree: If, cond: Tree, thenp: Tree, elsep: Tree)(implicit ctx: Context): Tree = cpy.If(tree, cond, thenp, elsep)

  def transformClosure(tree: Closure, env: List[Tree], meth: Tree, tpt: Tree)(implicit ctx: Context): Tree = cpy.Closure(tree, env, meth, tpt)

  def transformMatch(tree: Match, selector: Tree, cases: List[CaseDef])(implicit ctx: Context): Tree = cpy.Match(tree, selector, cases)

  def transformCaseDef(tree: CaseDef, pat: Tree, guard: Tree, body: Tree)(implicit ctx: Context): Tree = cpy.CaseDef(tree, pat, guard, body)

  def transformReturn(tree: Return, expr: Tree, from: Tree)(implicit ctx: Context): Tree = cpy.Return(tree, expr, from)

  def transformTry(tree: Try, expr: Tree, handler: Tree, finalizer: Tree)(implicit ctx: Context): Try = cpy.Try(tree, expr, handler, finalizer)

  def transformThrow(tree: Throw, expr: Tree)(implicit ctx: Context): Throw = cpy.Throw(tree, expr)

  def transformSeqLiteral(tree: SeqLiteral, elems: List[Tree])(implicit ctx: Context): SeqLiteral = cpy.SeqLiteral(tree, elems)

  def transformTypeTree(tree: TypeTree, original: Tree)(implicit ctx: Context): TypeTree = cpy.TypeTree(tree, original)

  def transformSingletonTypeTree(tree: SingletonTypeTree, ref: Tree)(implicit ctx: Context): SingletonTypeTree = cpy.SingletonTypeTree(tree, ref)

  def transformSelectFromTypeTree(tree: SelectFromTypeTree, qualifier: Tree, name: Name)(implicit ctx: Context): SelectFromTypeTree = cpy.SelectFromTypeTree(tree, qualifier, name)

  def transformAndTypeTree(tree: AndTypeTree, left: Tree, right: Tree)(implicit ctx: Context): AndTypeTree = cpy.AndTypeTree(tree, left, right)

  def transformOrTypeTree(tree: OrTypeTree, left: Tree, right: Tree)(implicit ctx: Context): OrTypeTree = cpy.OrTypeTree(tree, left, right)

  def transformRefinedTypeTree(tree: RefinedTypeTree, tpt: Tree, refinements: List[Tree])(implicit ctx: Context): RefinedTypeTree = cpy.RefinedTypeTree(tree, tpt, refinements)

  def transformAppliedTypeTree(tree: AppliedTypeTree, tpt: Tree, args: List[Tree])(implicit ctx: Context): AppliedTypeTree = cpy.AppliedTypeTree(tree, tpt, args)

  def transformByNameTypeTree(tree: ByNameTypeTree, result: Tree)(implicit ctx: Context): ByNameTypeTree = cpy.ByNameTypeTree(tree, result)

  def transformTypeBoundsTree(tree: TypeBoundsTree, lo: Tree, hi: Tree)(implicit ctx: Context): TypeBoundsTree = cpy.TypeBoundsTree(tree, lo, hi)

  def transformBind(tree: Bind, name: Name, body: Tree)(implicit ctx: Context): Bind = cpy.Bind(tree, name, body)

  def transformAlternative(tree: Alternative, trees: List[Tree])(implicit ctx: Context): Alternative = cpy.Alternative(tree, trees)

  def transformUnApply(tree: UnApply, fun: Tree, implicits: List[Tree], patterns: List[Tree])(implicit ctx: Context): UnApply = cpy.UnApply(tree, fun, implicits, patterns)

  def transformValDef(tree: ValDef, mods: Modifiers, name: TermName, tpt: Tree, rhs: Tree)(implicit ctx: Context): ValDef = cpy.ValDef(tree, mods, name, tpt, rhs)

  def transformDefDef(tree: DefDef, mods: Modifiers, name: TermName, tparams: List[TypeDef], vparams: List[List[ValDef]], tpt: Tree, rhs: Tree)(implicit ctx: Context): DefDef =
    cpy.DefDef(tree, mods, name, tparams, vparams, tpt, rhs)

  def transformTypeDef(tree: TypeDef, mods: Modifiers, name: TypeName, rhs: Tree, tparams: List[untpd.TypeDef] = Nil)(implicit ctx: Context): TypeDef = cpy.TypeDef(tree, mods, name, rhs, tparams)

  def transformTemplate(tree: Template, constr: DefDef, parents: List[Tree], self: ValDef, body: List[Tree])(implicit ctx: Context): Template = cpy.Template(tree, constr, parents, self, body)

  def transformImport(tree: Import, expr: Tree, selectors: List[untpd.Tree])(implicit ctx: Context): Import = cpy.Import(tree, expr, selectors)

  def transformPackageDef(tree: PackageDef, pid: RefTree, stats: List[Tree])(implicit ctx: Context): PackageDef = cpy.PackageDef(tree, pid, stats)

  def transformAnnotated(tree: Annotated, annot: Tree, arg: Tree)(implicit ctx: Context): Annotated = cpy.Annotated(tree, annot, arg)

  def transformSharedTree(tree: SharedTree, shared: Tree)(implicit ctx: Context): SharedTree = cpy.SharedTree(tree, shared)

  def transformThicket(tree: Thicket, trees: List[Tree])(implicit ctx: Context): Thicket = cpy.Thicket(tree, trees)
}

abstract class TreeTransformerPhase extends Phase {

  import tpd._

  def transformations: Seq[TreeTransformation]

  var sharedMemo: Map[SharedTree, SharedTree] = Map()


  override def run(implicit ctx: Context): Unit = {
    val curTree = ctx.compilationUnit.tpdTree
    val newTree = transform(curTree)
    ctx.compilationUnit.tpdTree = newTree
  }

  def transform(tree: Tree)(implicit ctx: Context): Tree = transform(tree, transformations)

  private def transform(tree: Tree, transformations: Seq[TreeTransformation])(implicit ctx: Context): Tree = {
    val thiz = this
    val t = tree
    if (transformations.isEmpty) {
      tree.putAttachment(TreeTransformation.Finished, this)
      tree
    }
    else {
      tree.getAttachment(TreeTransformation.Finished) match {
        case Some(thiz) => tree
        case None =>
          var tree: Tree = t
          var transformationsLeft = transformations
          while (!transformationsLeft.isEmpty) {
            val cur = transformationsLeft.head
            tree = tree match {
              case Ident(name) =>
                cur.transformIdent(tree.asInstanceOf[Ident], name)
              case Select(qualifier, name) =>
                cur.transformSelect(tree.asInstanceOf[Select], transform(qualifier.asInstanceOf[tpd.Tree], transformationsLeft), name)
              case This(qual) =>
                cur.transformThis(tree.asInstanceOf[This], qual)
              case Super(qual, mix) =>
                cur.transformSuper(tree.asInstanceOf[Super], transform(qual.asInstanceOf[tpd.Tree], transformationsLeft), mix)
              case Apply(fun, args) =>
                cur.transformApply(tree.asInstanceOf[Apply],
                  transform(fun.asInstanceOf[tpd.Tree], transformationsLeft),
                  transformL(args.asInstanceOf[List[tpd.Tree]], transformationsLeft))
              case TypeApply(fun, args) =>
                cur.transformTypeApply(tree.asInstanceOf[TypeApply],
                  transform(fun.asInstanceOf[tpd.Tree], transformationsLeft),
                  transformL(args.asInstanceOf[List[tpd.Tree]], transformationsLeft))
              case Literal(const) =>
                cur.transformLiteral(tree.asInstanceOf[Literal], const)
              case New(tpt) =>
                cur.transformNew(tree.asInstanceOf[New], transform(tpt.asInstanceOf[tpd.Tree], transformationsLeft))
              case Pair(left, right) =>
                cur.transformPair(tree.asInstanceOf[Pair],
                  transform(left.asInstanceOf[tpd.Tree], transformationsLeft),
                  transform(right.asInstanceOf[tpd.Tree], transformationsLeft))
              case Typed(expr, tpt) =>
                cur.transformTyped(tree.asInstanceOf[Typed],
                  transform(expr.asInstanceOf[tpd.Tree], transformationsLeft),
                  transform(tpt.asInstanceOf[tpd.Tree], transformationsLeft))
              case NamedArg(name, arg) =>
                cur.transformNamedArg(tree.asInstanceOf[NamedArg], name, transform(arg.asInstanceOf[tpd.Tree], transformationsLeft))
              case Assign(lhs, rhs) =>
                cur.transformAssign(tree.asInstanceOf[Assign],
                  transform(lhs.asInstanceOf[tpd.Tree], transformationsLeft),
                  transform(rhs.asInstanceOf[tpd.Tree], transformationsLeft))
              case Block(stats, expr) =>
                cur.transformBlock(tree.asInstanceOf[Block],
                  transformStats(stats.asInstanceOf[List[tpd.Tree]], transformationsLeft),
                  transform(expr.asInstanceOf[tpd.Tree], transformationsLeft))
              case If(cond, thenp, elsep) =>
                cur.transformIf(tree.asInstanceOf[If],
                  transform(cond.asInstanceOf[tpd.Tree], transformationsLeft),
                  transform(thenp.asInstanceOf[tpd.Tree], transformationsLeft),
                  transform(elsep.asInstanceOf[tpd.Tree], transformationsLeft))
              case Closure(env, meth, tpt) =>
                cur.transformClosure(tree.asInstanceOf[Closure],
                  transformL(env.asInstanceOf[List[tpd.Tree]], transformationsLeft),
                  transform(meth.asInstanceOf[tpd.Tree], transformationsLeft),
                  transform(tpt.asInstanceOf[tpd.Tree], transformationsLeft))
              case Match(selector, cases) =>
                cur.transformMatch(tree.asInstanceOf[Match],
                  transform(selector.asInstanceOf[tpd.Tree], transformationsLeft),
                  transformSubL(cases.asInstanceOf[List[tpd.CaseDef]], transformationsLeft))
              case CaseDef(pat, guard, body) =>
                cur.transformCaseDef(tree.asInstanceOf[CaseDef],
                  transform(pat.asInstanceOf[tpd.Tree], transformationsLeft),
                  transform(guard.asInstanceOf[tpd.Tree], transformationsLeft),
                  transform(body.asInstanceOf[tpd.Tree], transformationsLeft))
              case Return(expr, from) =>
                cur.transformReturn(tree.asInstanceOf[Return],
                  transform(expr.asInstanceOf[tpd.Tree], transformationsLeft),
                  transform(from.asInstanceOf[tpd.Tree], transformationsLeft))
              case Try(block, handler, finalizer) =>
                cur.transformTry(tree.asInstanceOf[Try],
                  transform(block.asInstanceOf[tpd.Tree], transformationsLeft),
                  transform(handler.asInstanceOf[tpd.Tree], transformationsLeft),
                  transform(finalizer.asInstanceOf[tpd.Tree], transformationsLeft))
              case Throw(expr) =>
                cur.transformThrow(tree.asInstanceOf[Throw],
                  transform(expr.asInstanceOf[tpd.Tree], transformationsLeft))
              case SeqLiteral(elems) =>
                cur.transformSeqLiteral(tree.asInstanceOf[SeqLiteral],
                  transformL(elems.asInstanceOf[List[tpd.Tree]], transformationsLeft))
              case TypeTree(original) =>
                cur.transformTypeTree(tree.asInstanceOf[TypeTree],
                  transform(original.asInstanceOf[tpd.Tree], transformationsLeft))
              case SingletonTypeTree(ref) =>
                cur.transformSingletonTypeTree(tree.asInstanceOf[SingletonTypeTree],
                  transform(ref.asInstanceOf[tpd.Tree], transformationsLeft))
              case SelectFromTypeTree(qualifier, name) =>
                cur.transformSelectFromTypeTree(tree.asInstanceOf[SelectFromTypeTree],
                  transform(qualifier.asInstanceOf[tpd.Tree], transformationsLeft), name)
              case AndTypeTree(left, right) =>
                cur.transformAndTypeTree(tree.asInstanceOf[AndTypeTree],
                  transform(left.asInstanceOf[tpd.Tree], transformationsLeft),
                  transform(right.asInstanceOf[tpd.Tree], transformationsLeft))
              case OrTypeTree(left, right) =>
                cur.transformOrTypeTree(tree.asInstanceOf[OrTypeTree],
                  transform(left.asInstanceOf[tpd.Tree], transformationsLeft),
                  transform(right.asInstanceOf[tpd.Tree], transformationsLeft))
              case RefinedTypeTree(tpt, refinements) =>
                cur.transformRefinedTypeTree(tree.asInstanceOf[RefinedTypeTree],
                  transform(tpt.asInstanceOf[tpd.Tree], transformationsLeft),
                  transformSubL(refinements.asInstanceOf[List[tpd.Tree]], transformationsLeft))
              case AppliedTypeTree(tpt, args) =>
                cur.transformAppliedTypeTree(tree.asInstanceOf[AppliedTypeTree],
                  transform(tpt.asInstanceOf[tpd.Tree], transformationsLeft),
                  transformL(args.asInstanceOf[List[tpd.Tree]], transformationsLeft))
              case ByNameTypeTree(result) =>
                cur.transformByNameTypeTree(tree.asInstanceOf[ByNameTypeTree],
                  transform(result.asInstanceOf[tpd.Tree], transformationsLeft))
              case TypeBoundsTree(lo, hi) =>
                cur.transformTypeBoundsTree(tree.asInstanceOf[TypeBoundsTree],
                  transform(lo.asInstanceOf[tpd.Tree], transformationsLeft),
                  transform(hi.asInstanceOf[tpd.Tree], transformationsLeft))
              case Bind(name, body) =>

                cur.transformBind(tree.asInstanceOf[Bind], name, transform(body.asInstanceOf[tpd.Tree], transformationsLeft))
              case Alternative(trees) =>
                cur.transformAlternative(tree.asInstanceOf[Alternative], transformL(trees.asInstanceOf[List[tpd.Tree]], transformationsLeft))
              case UnApply(fun, implicits, patterns) =>
                cur.transformUnApply(tree.asInstanceOf[UnApply],
                  transform(fun.asInstanceOf[tpd.Tree], transformationsLeft),
                  transformL(implicits.asInstanceOf[List[tpd.Tree]], transformationsLeft),
                  transformL(patterns.asInstanceOf[List[tpd.Tree]], transformationsLeft))
              case ValDef(mods, name, tpt, rhs) if !tree.isEmpty => // As a result of discussing with Martin :emptyValDefs shouldn't be copied
                cur.transformValDef(tree.asInstanceOf[ValDef],
                  mods.asInstanceOf[tpd.Modifiers],
                  name,
                  transform(tpt.asInstanceOf[tpd.Tree], transformationsLeft),
                  transform(rhs.asInstanceOf[tpd.Tree], transformationsLeft))
              case DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
                cur.transformDefDef(tree.asInstanceOf[DefDef],
                  mods.asInstanceOf[tpd.Modifiers],
                  name,
                  transformSubL(tparams.asInstanceOf[List[tpd.TypeDef]], transformationsLeft),
                  vparamss.mapConserve(x => transformSubL(x, transformationsLeft)),
                  transform(tpt.asInstanceOf[tpd.Tree], transformationsLeft),
                  transform(rhs.asInstanceOf[tpd.Tree], transformationsLeft))
              case tree@TypeDef(mods, name, rhs) =>
                cur.transformTypeDef(tree, mods.asInstanceOf[tpd.Modifiers], name, transform(rhs.asInstanceOf[tpd.Tree], transformationsLeft), tree.tparams)
              case Template(constr, parents, self, body) =>
                cur.transformTemplate(tree.asInstanceOf[Template],
                  transformSub(constr.asInstanceOf[tpd.DefDef], transformationsLeft),
                  transformL(parents.asInstanceOf[List[tpd.Tree]], transformationsLeft),
                  transformSub(self.asInstanceOf[tpd.ValDef], transformationsLeft),
                  transformStats(body.asInstanceOf[List[tpd.Tree]], transformationsLeft))
              case Import(expr, selectors) =>
                cur.transformImport(tree.asInstanceOf[Import],
                  transform(expr.asInstanceOf[tpd.Tree], transformationsLeft),
                  transformL(selectors.asInstanceOf[List[tpd.Tree]], transformationsLeft))
              case PackageDef(pid, stats) =>
                cur.transformPackageDef(tree.asInstanceOf[PackageDef],
                  transformSub(pid.asInstanceOf[tpd.RefTree], transformationsLeft),
                  transformStats(stats.asInstanceOf[List[tpd.Tree]], transformationsLeft))
              case Annotated(annot, arg) =>
                cur.transformAnnotated(tree.asInstanceOf[Annotated],
                  transform(annot.asInstanceOf[tpd.Tree], transformationsLeft),
                  transform(arg.asInstanceOf[tpd.Tree], transformationsLeft))
              case Thicket(trees) =>
                val trees1 = transformL(trees.asInstanceOf[List[tpd.Tree]], transformations) /// TODO
                if (trees1 eq trees) tree else Thicket(trees1)
              case tree@SharedTree(shared) =>
                sharedMemo get tree match {
                  case Some(tree1) => tree1
                  case None =>
                    val tree1 = cpy.SharedTree(tree, transform(shared.asInstanceOf[tpd.Tree], transformationsLeft))
                    sharedMemo = sharedMemo.updated(tree, tree1)
                    tree1
                }
              case EmptyTree => EmptyTree
              case _ => tree
            }

            transformationsLeft = transformationsLeft.tail
          }
          tree
      }

    }
  }

  def transformStats(trees: List[Tree], transformations: Seq[TreeTransformation])(implicit ctx: Context): List[Tree] =
    transformL(trees, transformations)(ctx)


  def transformL(trees: List[Tree], transformations: Seq[TreeTransformation])(implicit ctx: Context): List[Tree] = {
    flatten(trees mapConserve (x => transform(x, transformations)))

  }

  def transformSub[Tr <: Tree](tree: Tr, transformations: Seq[TreeTransformation])(implicit ctx: Context): Tr =
    transform(tree, transformations).asInstanceOf[Tr]

  def transformSubL[Tr <: Tree](trees: List[Tr], transformations: Seq[TreeTransformation])(implicit ctx: Context): List[Tr] =
    transformL(trees, transformations)(ctx).asInstanceOf[List[Tr]]


}


