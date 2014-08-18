package dotty.tools.dotc
package transform

import core._
import core.transform.Erasure.ErasedValueType
import Types._
import Contexts._
import Symbols._
import Decorators._
import StdNames.nme
import NameOps._
import language.implicitConversions

object SymUtils {
  implicit def decorateSymUtils(sym: Symbol): SymUtils = new SymUtils(sym)
}

/** A decorator that provides methods on symbols
 *  that are needed in the transformer pipeline.
 */
class SymUtils(val self: Symbol) extends AnyVal {

  def isTypeTestOrCast(implicit ctx: Context): Boolean =
    self == defn.Any_asInstanceOf || self == defn.Any_isInstanceOf
}