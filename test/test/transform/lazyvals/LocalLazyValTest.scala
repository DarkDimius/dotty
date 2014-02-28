package test.transform.lazyvals

import scala.reflect.io._
import dotty.tools.dotc.util._
import dotty.tools.dotc.core._
import dotty.tools.dotc.parsing._
import Tokens._, Parsers._
import dotty.tools.dotc.ast.untpd._
import org.junit.Test
import scala.collection.mutable.ListBuffer
import test.DottyTest
import dotty.tools.dotc.Compiler
import dotty.tools.dotc.transform.LocalLazyVals
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.core.Phases.Phase
import org.junit.Assert

class LocalLazyValTest extends DottyTest {

  var lastTree:tpd.Tree = _

  @Test
  def localInt = {
    checkCompile("LocalLazyVals", List("tests/pos/lazyVals/LocalIntLV.scala")){ tree =>
      Assert.assertTrue("local lazy int rewritten to class creation", tree.toString.contains(
      "ValDef(Modifiers(,,List()),s$lzy1,TypeTree[TypeRef(ThisType(module class runtime),LazyInt)],Apply(Select(New(TypeTree[TypeRef(ThisType(module class runtime),LazyInt)]),<init>),List(Literal(Constant(1)))))"
      ))
    }
  }
}
