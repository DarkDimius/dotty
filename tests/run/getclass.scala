class ValueClass(val i: Integer) extends AnyVal
class SomeClass

object Test {
  def main(args: Array[String]): Unit = {
    val cls: Predef.Class[_] = new SomeClass().getClass
    val valCls: Predef.Class[_] = new ValueClass(1).getClass
    val iCls: Class[Int] = 1.getClass
    val f1: Function2[Int, Int, Unit] = (a: Int, b: Int) => println(a + b)
    val f2: Function1[Int, Boolean] = (a: Int) => a % 2 == 0

    println("Value types:")
    println(().getClass)
    println(true.getClass)
    println(1.asInstanceOf[Byte].getClass)
    println(1.asInstanceOf[Short].getClass)
    println('a'.getClass)
    println(1.getClass)
    println(1L.getClass)
    println(1f.getClass)
    println(1d.getClass)

    println("Class types")
    println(new SomeClass().getClass)
    println(new ValueClass(1).getClass)
    println(List(Array(1f)).getClass)
    println(("a", Map(1 -> "b")).getClass)

    println("Arrays:")
    println(Array(()).getClass)
    println(Array(1).getClass)
    println(Array(1d).getClass)
    println(Array(List("1")).getClass)

    println("Functions:")
    println(f1.getClass)
    println(f2.getClass)
  }
}
