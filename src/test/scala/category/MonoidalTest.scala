package parrot
package category

class MonoidalTest extends CategorySuite {

  // =========================================================================
  // Monoidal Laws on Function
  // =========================================================================

  private val FunctionLaws = Monoidal.FunctionIsMonoidal.MonoidalLaws

  test("Function is Monoidal: tensor identity law") {
    val _ = assert(FunctionLaws.tensorIdentity[Int, String])
    val _ = assert(FunctionLaws.tensorIdentity[Double, Boolean])
    assert(FunctionLaws.tensorIdentity[String, (Int, Int)])
  }

  test("Function is Monoidal: tensor composition law") {
    // Arithmetic & string conversions
    val f1: Int => String     = i => if i >= 0 then s"+$i" else s"-$i"
    val f2: String => Boolean = _.length > 2
    val g1: Double => Int     = d => math.round(d).toInt
    val g2: Int => String     = n => s"num:$n"
    val _                     = assert(FunctionLaws.tensorComposition(f1, f2, g1, g2))

    // Boundary cases and constants
    val f1Const: Int => String     = _ => "fixed"
    val f2Const: String => Boolean = _ => true
    val g1Const: Double => Int     = _ => 0
    val g2Const: Int => String     = _ => "zero"
    assert(FunctionLaws.tensorComposition(f1Const, f2Const, g1Const, g2Const))
  }

  test("Function is Monoidal: associator naturality law") {
    val f: Int => String     = i => if i % 2 == 0 then s"even:$i" else s"odd:$i"
    val g: Boolean => Int    = if _ then 1 else 0
    val h: Double => Boolean = _ > 0.0
    val _                    = assert(FunctionLaws.associatorNaturality(f, g, h))

    val f2: String => Int     = _.length
    val g2: Int => Boolean    = _ != 0
    val h2: Boolean => String = if _ then "T" else "F"
    assert(FunctionLaws.associatorNaturality(f2, g2, h2))
  }

  test("Function is Monoidal: left unitor naturality law") {
    val f1: Int => String = i => if i >= 0 then s"pos:$i" else s"neg:$i"
    val f2: String => Int = _.length
    val _                 = assert(FunctionLaws.leftUnitorNaturality(f1))
    assert(FunctionLaws.leftUnitorNaturality(f2))
  }

  test("Function is Monoidal: right unitor naturality law") {
    val f1: Int => String = i => if i >= 0 then s"pos:$i" else s"neg:$i"
    val f2: String => Int = _.length
    val _                 = assert(FunctionLaws.rightUnitorNaturality(f1))
    assert(FunctionLaws.rightUnitorNaturality(f2))
  }

  test("Function is Monoidal: triangle law") {
    val _ = assert(FunctionLaws.triangle[Int, String])
    val _ = assert(FunctionLaws.triangle[String, Boolean])
    assert(FunctionLaws.triangle[Double, (Int, String)])
  }

  test("Function is Monoidal: pentagon law") {
    val _ = assert(FunctionLaws.pentagon[Int, String, Boolean, Double])
    assert(FunctionLaws.pentagon[String, Int, Double, Boolean])
  }

  test("Function is Monoidal: unitor and associator isomorphism laws") {
    val _ = assert(FunctionLaws.leftUnitorIsomorphism[Int])
    val _ = assert(FunctionLaws.leftUnitorIsomorphism[String])
    val _ = assert(FunctionLaws.leftUnitorIsomorphism[(Int, Boolean)])

    val _ = assert(FunctionLaws.rightUnitorIsomorphism[Int])
    val _ = assert(FunctionLaws.rightUnitorIsomorphism[String])
    val _ = assert(FunctionLaws.rightUnitorIsomorphism[(Int, Boolean)])

    val _ = assert(FunctionLaws.associatorIsomorphism[Int, String, Boolean])
    assert(FunctionLaws.associatorIsomorphism[Double, Int, String])
  }
}
