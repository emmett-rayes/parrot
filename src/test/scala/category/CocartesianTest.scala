package parrot
package category

class CocartesianTest extends CategorySuite {

  // =========================================================================
  // Cocartesian Laws on Function
  // =========================================================================

  private val FunctionLaws = Cocartesian.FunctionIsCocartesian.CocartesianLaws

  given NothingFunctionIsEq: [A] => ((Nothing => A) is Eq) =
    (_, _) => true

  test("Function is Cocartesian: left injection law") {
    // Arithmetic & linear
    val f1: Int => String     = i => s"val:$i"
    val g1: Boolean => String = b => if b then "val:true" else "val:false"
    val _                     = assert(FunctionLaws.leftInjection(f1, g1))

    // Multi-branching & boundary conditions
    val f2: Int => String    = i => if i < 0 then "neg" else if i == 0 then "zero" else "pos"
    val g2: Double => String = d => if d > 0.0 then "pos" else "non-pos"
    val _                    = assert(FunctionLaws.leftInjection(f2, g2))

    // Constant functions
    val f3: Int => String    = _ => "const"
    val g3: String => String = _ => "const"
    val _                    = assert(FunctionLaws.leftInjection(f3, g3))

    // String & tuple transformations
    val f4: String => Int           = _.length
    val g4: ((Int, Boolean)) => Int = p => p._1 * 2
    assert(FunctionLaws.leftInjection(f4, g4))
  }

  test("Function is Cocartesian: right injection law") {
    // Arithmetic & linear
    val f1: Int => String     = i => s"val:$i"
    val g1: Boolean => String = b => if b then "val:true" else "val:false"
    val _                     = assert(FunctionLaws.rightInjection(f1, g1))

    // Multi-branching & boundary conditions
    val f2: Int => String    = i => if i < 0 then "neg" else if i == 0 then "zero" else "pos"
    val g2: Double => String = d => if d > 0.0 then "pos" else "non-pos"
    val _                    = assert(FunctionLaws.rightInjection(f2, g2))

    // Constant functions
    val f3: Int => String    = _ => "const"
    val g3: String => String = _ => "const"
    val _                    = assert(FunctionLaws.rightInjection(f3, g3))

    // String & tuple transformations
    val f4: String => Int           = _.length
    val g4: ((Int, Boolean)) => Int = p => p._1 * 2
    assert(FunctionLaws.rightInjection(f4, g4))
  }

  test("Function is Cocartesian: sum uniqueness law") {
    val _ = assert(FunctionLaws.sumUniqueness[Int, String])
    val _ = assert(FunctionLaws.sumUniqueness[Double, Boolean])
    assert(FunctionLaws.sumUniqueness[String, (Int, Int)])
  }

  test("Function is Cocartesian: initial uniqueness law") {
    val f1: Nothing => Unit             = Cocartesian.FunctionIsCocartesian.absurd[Unit]
    val f2: Nothing => Int              = n => n
    val f3: Nothing => String           = n => n
    val f4: Nothing => ((Int, Boolean)) = n => n
    val _                               = assert(FunctionLaws.initialUniqueness(f1))
    val _                               = assert(FunctionLaws.initialUniqueness(f2))
    val _                               = assert(FunctionLaws.initialUniqueness(f3))
    assert(FunctionLaws.initialUniqueness(f4))
  }

  test("Function is Cocartesian: fold left and right injection laws") {
    val _ = assert(FunctionLaws.foldLeft[Int])
    val _ = assert(FunctionLaws.foldLeft[String])
    val _ = assert(FunctionLaws.foldLeft[(Int, Boolean)])

    val _ = assert(FunctionLaws.foldRight[Int])
    val _ = assert(FunctionLaws.foldRight[String])
    assert(FunctionLaws.foldRight[(Int, Boolean)])
  }
}
