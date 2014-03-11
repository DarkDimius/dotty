package dotty.tools.dotc.transform

import dotty.tools.dotc.core._
import Symbols._
import scala.Some
import dotty.tools.dotc.transform.TreeTransforms.{NXTransformations, TransformerInfo, TreeTransform, TreeTransformer}
import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.core.Contexts.Context
import scala.collection.mutable
import dotty.tools.dotc.core.Names.Name
import NameOps._

object PostTyperTransformers {

  import tpd.{TreeTransformer => _, _}

  trait CompanionNeededPredicate {
    def apply(forClass: TypeDef)(implicit ctx: Context): Boolean
  }

  trait CompanionObjectNeeded {
    def companionObjectRequiredPredicate: CompanionNeededPredicate
  }

  /** A trait that's assumed by the transformers that run right after typer.
    * Ensures that trees are normalized when seen by other transforms. This means:
    * (1) All module class definitions appear after their companion class definitions
    * (2) There are no import clauses or named arguments
    * (3) All trees designating types are instances of TypeTree
    *
    * if some transform needs a companion object to exist, it should extend CompanionObjectNeeded trait.
    * Both symbols and trees will be injected for required non-existent companion objects.
    * Note, that all predicates are acquired before executing any 'prepare' methods.
    */
  abstract class PostTyperTransformer extends TreeTransformer {

    var predicates: Array[CompanionNeededPredicate] = _

    /** Reorder statements so that module classes always come after their companion classes, add missing companion classes */
    def reorder(stats: List[Tree])(implicit ctx: Context, info: TransformerInfo): List[Tree] = {
      val moduleClassDefs = mutable.Map[Name, Tree]()
      def reorder0(stats: List[Tree]): List[Tree] = {
        stats match {
          case (stat: TypeDef) :: stats1 if stat.symbol.isClass =>
            if (stat.symbol is Flags.Module) {
              moduleClassDefs += (stat.name -> stat)
              val stats1r = reorder0(stats1)
              if (moduleClassDefs contains stat.name) stat :: stats1r else stats1r
            }
            else {
              val mclsName = stat.name.moduleClassName
              moduleClassDefs remove mclsName match {
                case Some(mcdef) => stat :: mcdef :: reorder0(stats1)
                case None => {
                  val tail = reorder0(stats1)
                  if ((!moduleClassDefs.contains(mclsName)) && predicates.exists(_(stat))) {
                    val moduleSymbol = ctx.newCompleteModuleSymbol(stat.symbol.owner, stat.name.toTermName, Flags.Synthetic, Flags.Synthetic, List(defn.ObjectClass.typeRef), Scopes.newScope)

                    if(moduleSymbol.owner.isClass) moduleSymbol.entered

                    val companion = tpd.ModuleDef(moduleSymbol, List(EmptyTree))
                    stat :: companion :: tail
                  }
                  else stat :: tail
                }
              }
            }
          case stat :: stats1 => stat :: reorder0(stats1)
          case Nil => Nil
        }
      }
      reorder0(stats)
    }

    override def transform(t: tpd.Tree)(implicit ctx: Context): tpd.Tree = {
      val initialTransformations = transformations.zipWithIndex.map(x => x._1(this, x._2))
      predicates = initialTransformations.filter(_.isInstanceOf[CompanionObjectNeeded]).map(x => x.asInstanceOf[CompanionObjectNeeded].companionObjectRequiredPredicate)
      transform(t, new TransformerInfo(initialTransformations, new NXTransformations(initialTransformations)), 0)
    }
    override def transformStats(trees: List[tpd.Tree], info: TransformerInfo, current: Int)(implicit ctx: Context): List[tpd.Tree] =
      super.transformStats(reorder(trees)(ctx, info), info, current)

    override def transform(tree: tpd.Tree, info: TransformerInfo, cur: Int)(implicit ctx: Context): tpd.Tree = tree match {
      case tree: Import => EmptyTree
      case tree: NamedArg => super.transform(tree.arg, info, cur)
      case tree: TypeTree => super.transform(tree, info, cur)
      case tree => super.transform(if (tree.isType) TypeTree(tree.tpe) else tree, info, cur)
    }
  }

}