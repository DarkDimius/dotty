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
        
      case poly: PolyType => {

        val pparams = (0 until poly.paramNames.length).toList map (PolyParam(poly, _))
        val newNames = specialisedTypes.values.map(suffix => (tree.name + suffix).toTermName) // or `toTypeName` ?
        val nameToType = specialisedTypes map (x => (tree.name + x._2).toTermName -> x._1)
        val newSyms = newNames.map(ctx.newSymbol(tree.symbol.owner, _, tree.symbol.flags | Flags.Synthetic, poly.instantiate(specialisedTypes.keys.toList))) //  TODO is the arg to instantiate correct ?
        val ttmaps = newSyms.map(newSymbol =>
          new TreeTypeMap(
            typeMap = rewireType(_).substDealias(pparams map (_.typeSymbol), List(nameToType(newSymbol.name))), // How about `pparams map (_.binder.paramNames)` for the 1st argument ?
            oldOwners = List(tree.symbol),
            newOwners = List(newSymbol)
          )
        ).toList
        val ss = ttmaps map (_ apply tree)
        Thicket(tree::ss) // Could there be an issue when casting `DefDef`s into `Tree`s ?
      }
      case _ => tree
    }
  }
}