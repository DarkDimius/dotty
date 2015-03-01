package dotty.tools.dotc.transform

import dotty.tools.dotc.ast.TreeTypeMap
import dotty.tools.dotc.ast.tpd._
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.Flags
import dotty.tools.dotc.core.Types._
import dotty.tools.dotc.transform.TreeTransforms.{TransformerInfo, MiniPhaseTransform}
import dotty.tools.dotc.core.Decorators._

class TypeSpecializer extends MiniPhaseTransform {
  
  override def phaseName = "Type Specializer"
  
  private final def specialisedTypes(implicit ctx: Context) =
    Map(ctx.definitions.ByteType -> "$mcB$sp",
    ctx.definitions.BooleanType -> "$mcZ$sp",
    ctx.definitions.ShortType -> "$mcS$sp",
    ctx.definitions.IntType -> "$mcI$sp",
    ctx.definitions.LongType -> "$mcJ$sp",
    ctx.definitions.FloatType -> "$mcF$sp",
    ctx.definitions.DoubleType -> "$mcD$sp",
    ctx.definitions.CharType -> "$mcC$sp",
    ctx.definitions.UnitType -> "$mcV$sp")
  
  override def transformDefDef(tree: DefDef)(implicit ctx: Context, info: TransformerInfo): Tree = {

    def rewireType(tpe: Type) = tpe match {
        case tpe: TermRef => tpe.widen
        case _ => tpe
      }
    
    tree.tpe.widen match {
        
      case poly: PolyType => { // PolyType is the type of methods with at least one argument

        val pparams = poly.paramNames.zipWithIndex.map(x => new PolyParam(poly, x._2).asInstanceOf[Type])

        def tpMap(tp: Type): Type = rewireType(tp).substDealias(List(tree.symbol.owner), pparams)

        val newNames = specialisedTypes.values.map(suffix => (tree.name + suffix).toTermName)

        val newSyms = newNames.map(name => ctx.newSymbol(tree.symbol.owner, name, tree.symbol.flags | Flags.Synthetic, poly.instantiate(specialisedTypes.keys.toList)))

        val ttmaps = newSyms.map(newSym => new TreeTypeMap(typeMap = tpMap, oldOwners = List(tree.symbol), newOwners = List(newSym))).toList

        val ss = for (ttmap <- ttmaps) yield ttmap apply tree
        Thicket(tree::ss) // Could there be an issue when casting `DefDef`s into `Tree`s ? Tests seem to suggest it.
      }
        
      case _ => tree
    }
  }
}