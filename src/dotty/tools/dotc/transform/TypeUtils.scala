package dotty.tools.dotc
package transform

import core._
import Types._
import Contexts._
import Symbols._
import Decorators._
import StdNames.nme
import NameOps._
import dotty.tools.dotc.ast.Trees.Tree
import dotty.tools.dotc.ast.tpd
import language.implicitConversions
import scala.annotation.tailrec

object TypeUtils {
  implicit def decorateTypeUtils(tpe: Type): TypeUtils = new TypeUtils(tpe)

  @tailrec
  def sameTypes(trees: List[tpd.Tree], trees1: List[tpd.Tree]): Boolean = {
    if (trees.isEmpty) trees.isEmpty
    else if (trees1.isEmpty) trees.isEmpty
    else (trees.head.tpe eq trees1.head.tpe) && sameTypes(trees.tail, trees1.tail)
  }
}

/** A decorator that provides methods for type transformations
 *  that are needed in the transofmer pipeline (not needed right now)
 */
class TypeUtils(val self: Type) extends AnyVal {
  import TypeUtils._

}