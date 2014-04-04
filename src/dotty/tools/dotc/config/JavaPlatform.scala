package dotty.tools
package dotc
package config

import io.{AbstractFile,ClassPath,JavaClassPath,MergedClassPath,DeltaClassPath}
import ClassPath.{ JavaContext, DefaultJavaContext }
import core.Contexts._
import core.SymDenotations._, core.Symbols._, core.{SymbolLoader, ClassfileLoader}
import dotty.tools.dotc.core.StdNames._

class JavaPlatform extends Platform {

  private var currentClassPath: Option[MergedClassPath] = None

  def classPath(implicit ctx: Context): ClassPath = {
    if (currentClassPath.isEmpty)
      currentClassPath = Some(new PathResolver().result)
    currentClassPath.get
  }
  def externalEquals(implicit ctx: Context): Symbol          = defn.BoxesRunTimeClass.requiredMethod(nme.equals_)
  def externalEqualsNumNum(implicit ctx: Context): Symbol    = defn.BoxesRunTimeClass.requiredMethod(nme.equalsNumNum)
  def externalEqualsNumChar(implicit ctx: Context): Symbol   = defn.BoxesRunTimeClass.requiredMethod(nme.equalsNumChar)
  def externalEqualsNumObject(implicit ctx: Context): Symbol = defn.BoxesRunTimeClass.requiredMethod(nme.equalsNumObject)

  /** Update classpath with a substituted subentry */
  def updateClassPath(subst: Map[ClassPath, ClassPath]) =
    currentClassPath = Some(new DeltaClassPath(currentClassPath.get, subst))

  def rootLoader(root: TermSymbol)(implicit ctx: Context): SymbolLoader = new ctx.base.loaders.PackageLoader(root, classPath)

  /** We could get away with excluding BoxedBooleanClass for the
   *  purpose of equality testing since it need not compare equal
   *  to anything but other booleans, but it should be present in
   *  case this is put to other uses.
   */
  def isMaybeBoxed(sym: Symbol)(implicit ctx: Context) = {
    val d = defn
    import d._
    (sym == ObjectClass) ||
    (sym == JavaSerializableClass) ||
    (sym == ComparableClass) ||
    (sym derivesFrom BoxedNumberClass) ||
    (sym derivesFrom BoxedCharClass) ||
    (sym derivesFrom BoxedBooleanClass)
  }

  def newClassLoader(bin: AbstractFile)(implicit ctx: Context): SymbolLoader =
    new ClassfileLoader(bin)
}
