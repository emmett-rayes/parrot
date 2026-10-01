package parrot
package category

class StrongTest extends CategorySuite {

  // =========================================================================
  // Strong Laws on Function
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
}
