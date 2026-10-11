package parrot
package category

class StrongTest extends CategorySuite {

  // =========================================================================
  // 1. Strong Laws on Function
  // =========================================================================

  private val FunctionLaws = Strong.FunctionIsStrong.StrongLaws

  test("Function is Strong: first naturality law") {
    val p: Int => String    = i => s"val:$i"
    val f: Boolean => Int   = if _ then 1 else 0
    val g: String => Double = _.length.toDouble
    val _                   = assert(FunctionLaws.firstNaturality[Int, String, Boolean, Double, Int](p, f, g))
    assert(FunctionLaws.firstNaturality[Int, String, Boolean, Double, String](p, f, g))
  }

  test("Function is Strong: second naturality law") {
    val p: Int => String    = i => s"val:$i"
    val f: Boolean => Int   = if _ then 1 else 0
    val g: String => Double = _.length.toDouble
    val _                   = assert(FunctionLaws.secondNaturality[Int, String, Boolean, Double, Int](p, f, g))
    assert(FunctionLaws.secondNaturality[Int, String, Boolean, Double, String](p, f, g))
  }

  test("Function is Strong: first unitality law") {
    val p1: Int => String = i => s"num:$i"
    val p2: String => Int = _.length
    val _                 = assert(FunctionLaws.firstUnitality(p1))
    assert(FunctionLaws.firstUnitality(p2))
  }

  test("Function is Strong: second unitality law") {
    val p1: Int => String = i => s"num:$i"
    val p2: String => Int = _.length
    val _                 = assert(FunctionLaws.secondUnitality(p1))
    assert(FunctionLaws.secondUnitality(p2))
  }

  test("Function is Strong: first associativity law") {
    val p: Int => String = i => s"num:$i"
    val _                = assert(FunctionLaws.firstAssociativity[Int, String, Boolean, Double](p))
    assert(FunctionLaws.firstAssociativity[Int, String, String, Int](p))
  }

  test("Function is Strong: second associativity law") {
    val p: Int => String = i => s"num:$i"
    val _                = assert(FunctionLaws.secondAssociativity[Int, String, Boolean, Double](p))
    assert(FunctionLaws.secondAssociativity[Int, String, String, Int](p))
  }

  // =========================================================================
  // 2. Strong Laws on Function (Lazy Cartesian / LazyTuple2)
  // =========================================================================

  private val LazyFunctionInstance = Strong.FunctionIsLazyStrong
  private val LazyFunctionLaws     = LazyFunctionInstance.StrongLaws

  test("Function is Lazy Strong: first and second evaluation") {
    val p: Int => String                                                 = i => s"val:$i"
    val lazyFirst: LazyTuple2[Int, String] => LazyTuple2[String, String] =
      LazyFunctionInstance.first[Int, String, String](p)
    val lazySecond: LazyTuple2[String, Int] => LazyTuple2[String, String] =
      LazyFunctionInstance.second[Int, String, String](p)

    val t1 = LazyTuple2(10, "hello")
    val r1 = lazyFirst(t1)
    val _  = assert(r1._1 == "val:10" && r1._2 == "hello")

    val t2 = LazyTuple2("hello", 10)
    val r2 = lazySecond(t2)
    assert(r2._1 == "hello" && r2._2 == "val:10")
  }

  test("Function is Lazy Strong: laziness preservation in first and second") {
    val p: Int => String                                                 = i => s"val:$i"
    val lazyFirst: LazyTuple2[Int, String] => LazyTuple2[String, String] =
      LazyFunctionInstance.first[Int, String, String](p)
    val lazySecond: LazyTuple2[String, Int] => LazyTuple2[String, String] =
      LazyFunctionInstance.second[Int, String, String](p)

    var evaluated1 = false
    val t1         = LazyTuple2(10, { evaluated1 = true; "side-effect" })
    val r1         = lazyFirst(t1)
    val _          = assert(!evaluated1 && r1._1 == "val:10")

    var evaluated2 = false
    val t2         = LazyTuple2({ evaluated2 = true; "side-effect" }, 10)
    val r2         = lazySecond(t2)
    assert(!evaluated2 && r2._2 == "val:10")
  }

  test("Function is Lazy Strong: first naturality law") {
    val p: Int => String    = i => s"val:$i"
    val f: Boolean => Int   = if _ then 1 else 0
    val g: String => Double = _.length.toDouble
    val _                   = assert(LazyFunctionLaws.firstNaturality[Int, String, Boolean, Double, Int](p, f, g))
    assert(LazyFunctionLaws.firstNaturality[Int, String, Boolean, Double, String](p, f, g))
  }

  test("Function is Lazy Strong: second naturality law") {
    val p: Int => String    = i => s"val:$i"
    val f: Boolean => Int   = if _ then 1 else 0
    val g: String => Double = _.length.toDouble
    val _                   = assert(LazyFunctionLaws.secondNaturality[Int, String, Boolean, Double, Int](p, f, g))
    assert(LazyFunctionLaws.secondNaturality[Int, String, Boolean, Double, String](p, f, g))
  }

  test("Function is Lazy Strong: first unitality law") {
    val p1: Int => String = i => s"num:$i"
    val p2: String => Int = _.length
    val _                 = assert(LazyFunctionLaws.firstUnitality(p1))
    assert(LazyFunctionLaws.firstUnitality(p2))
  }

  test("Function is Lazy Strong: second unitality law") {
    val p1: Int => String = i => s"num:$i"
    val p2: String => Int = _.length
    val _                 = assert(LazyFunctionLaws.secondUnitality(p1))
    assert(LazyFunctionLaws.secondUnitality(p2))
  }

  test("Function is Lazy Strong: first associativity law") {
    val p: Int => String = i => s"num:$i"
    val _                = assert(LazyFunctionLaws.firstAssociativity[Int, String, Boolean, Double](p))
    assert(LazyFunctionLaws.firstAssociativity[Int, String, String, Int](p))
  }

  test("Function is Lazy Strong: second associativity law") {
    val p: Int => String = i => s"num:$i"
    val _                = assert(LazyFunctionLaws.secondAssociativity[Int, String, Boolean, Double](p))
    assert(LazyFunctionLaws.secondAssociativity[Int, String, String, Int](p))
  }
}
