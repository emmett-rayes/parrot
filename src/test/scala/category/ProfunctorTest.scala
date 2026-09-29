package parrot
package category

class ProfunctorTest extends CategorySuite {

  // =========================================================================
  // 1. Profunctor Laws on `=:=`
  // =========================================================================

  private val TypeEqLaws = Profunctor.TypeEqIsProfunctor.ProfunctorLaws

  test("=:= is Profunctor: identity law") {
    val refl = summon[Int =:= Int]
    assert(TypeEqLaws.identity(refl))
  }

  test("=:= is Profunctor: composition law") {
    val refl = summon[Int =:= Int]
    assert(TypeEqLaws.composition(refl, refl, refl, refl, refl))
  }

  // =========================================================================
  // 2. Profunctor Laws on Function
  // =========================================================================

  private val FunctionLaws = Profunctor.FunctionIsProfunctor.ProfunctorLaws

  test("Function is Profunctor: identity law") {
    val p1: Int => String = i => if i >= 0 then s"pos:$i" else s"neg:$i"
    val p2: Int => String = _ => "const"
    val p3: String => Int = _.length
    val _                 = assert(FunctionLaws.identity(p1))
    val _                 = assert(FunctionLaws.identity(p2))
    assert(FunctionLaws.identity(p3))
  }

  test("Function is Profunctor: composition law") {
    val p1: Int => String      = n => if n % 2 == 0 then s"even:$n" else s"odd:$n"
    val f1_1: Double => Int    = d => math.round(d).toInt
    val f2_1: String => Double = _.length.toDouble
    val g1_1: String => Int    = _.length
    val g2_1: Int => Boolean   = _ > 5
    val _                      = assert(FunctionLaws.composition(p1, f1_1, g1_1, f2_1, g2_1))

    val p2: Int => String      = _ => "fixed"
    val f1_2: Double => Int    = _ => 0
    val f2_2: String => Double = _ => 0.0
    val g1_2: String => Int    = _ => 1
    val g2_2: Int => Boolean   = _ => true
    assert(FunctionLaws.composition(p2, f1_2, g1_2, f2_2, g2_2))
  }
}
