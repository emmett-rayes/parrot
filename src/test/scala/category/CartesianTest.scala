package parrot
package category

class CartesianTest extends CategorySuite {

  // =========================================================================
  // Cartesian Laws on Function
  // =========================================================================

  private val FunctionLaws = Cartesian.FunctionIsCartesian.CartesianLaws

  test("Function is Cartesian: first projection law") {
    // Arithmetic & linear
    val f1: Int => String  = i => s"val:$i"
    val g1: Int => Boolean = i => i % 2 == 0
    val _                  = assert(FunctionLaws.firstProjection(f1, g1))

    // Multi-branching & boundary conditions
    val f2: Int => String  = i => if i < 0 then "neg" else if i == 0 then "zero" else "pos"
    val g2: Int => Boolean = i => Math.abs(i) > 10
    val _                  = assert(FunctionLaws.firstProjection(f2, g2))

    // Constant functions
    val f3: Int => String  = _ => "const"
    val g3: Int => Boolean = _ => false
    val _                  = assert(FunctionLaws.firstProjection(f3, g3))

    // String & tuple transformations
    val f4: String => Int     = _.length
    val g4: String => Boolean = _.reverse.nonEmpty
    assert(FunctionLaws.firstProjection(f4, g4))
  }

  test("Function is Cartesian: second projection law") {
    // Arithmetic & linear
    val f1: Int => String  = i => s"val:$i"
    val g1: Int => Boolean = i => i % 2 == 0
    val _                  = assert(FunctionLaws.secondProjection(f1, g1))

    // Multi-branching & boundary conditions
    val f2: Int => String  = i => if i < 0 then "neg" else if i == 0 then "zero" else "pos"
    val g2: Int => Boolean = i => Math.abs(i) > 10
    val _                  = assert(FunctionLaws.secondProjection(f2, g2))

    // Constant functions
    val f3: Int => String  = _ => "const"
    val g3: Int => Boolean = _ => false
    val _                  = assert(FunctionLaws.secondProjection(f3, g3))

    // String & tuple transformations
    val f4: String => Int     = _.length
    val g4: String => Boolean = _.reverse.nonEmpty
    assert(FunctionLaws.secondProjection(f4, g4))
  }

  test("Function is Cartesian: product uniqueness law") {
    val _ = assert(FunctionLaws.productUniqueness[Int, String])
    val _ = assert(FunctionLaws.productUniqueness[Double, Boolean])
    assert(FunctionLaws.productUniqueness[String, (Int, Int)])
  }

  test("Function is Cartesian: terminal uniqueness law") {
    val f1: Int => Unit              = _ => ()
    val f2: Int => Unit              = i => { val _ = i * 2 + 1; () }
    val f3: String => Unit           = s => { val _ = s.toLowerCase; () }
    val f4: ((Int, Boolean)) => Unit = p => { val _ = p._1; () }
    val _                            = assert(FunctionLaws.terminalUniqueness(f1))
    val _                            = assert(FunctionLaws.terminalUniqueness(f2))
    val _                            = assert(FunctionLaws.terminalUniqueness(f3))
    assert(FunctionLaws.terminalUniqueness(f4))
  }

  test("Function is Cartesian: diagonal first and second projection laws") {
    val _ = assert(FunctionLaws.diagonalFirst[Int])
    val _ = assert(FunctionLaws.diagonalFirst[String])
    val _ = assert(FunctionLaws.diagonalFirst[(Int, Boolean)])

    val _ = assert(FunctionLaws.diagonalSecond[Int])
    val _ = assert(FunctionLaws.diagonalSecond[String])
    assert(FunctionLaws.diagonalSecond[(Int, Boolean)])
  }
}
