package test.transform.lazyvals

import org.junit.Test
import test.DottyTest
import dotty.tools.dotc.ast.tpd
import org.junit.Assert

class LocalLazyValTest extends DottyTest {

  var lastTree:tpd.Tree = _

  @Test
  def localInt = {
    checkCompile("LocalLazyVals", List("tests/pos/lazyVals/LocalIntLV.scala")){ (tree, ctx) =>
      Assert.assertTrue("local lazy int rewritten to class creation", tree.toString.contains(
      "ValDef(Modifiers(,,List()),s$lzy1,TypeTree[TypeRef(ThisType(module class runtime),LazyInt)],Apply(Select(New(TypeTree[TypeRef(ThisType(module class runtime),LazyInt)]),<init>),List(Literal(Constant(1)))))"
      ))
    }
  }
}
