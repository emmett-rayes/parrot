package parrot
package category

class PromonadTest extends CategorySuite {

  // =========================================================================
  // 1. Promonad Laws on `=:=`
  // =========================================================================

  private val TypeEqLaws = Promonad.TypeEqIsPromonad.PromonadLaws

  test("=:= is Promonad: unit naturality law") {
    val refl = summon[Int =:= Int]
    assert(TypeEqLaws.unitNaturality(refl, refl, refl))
  }

  test("=:= is Promonad: multiplication naturality law") {
    val refl = summon[Int =:= Int]
    assert(TypeEqLaws.multiplicationNaturality[Int, Int, Int, Int, Int](refl, refl))
  }

  test("=:= is Promonad: left identity law") {
    assert(TypeEqLaws.leftIdentity[Int, Int])
  }

  test("=:= is Promonad: right identity law") {
    assert(TypeEqLaws.rightIdentity[Int, Int])
  }

  test("=:= is Promonad: associativity law") {
    assert(TypeEqLaws.associativity[Int, Int, Int, Int])
  }

  test("=:= is Promonad: coend wedge balancing law") {
    val refl = summon[Int =:= Int]
    assert(TypeEqLaws.wedge[Int, Int, Int, Int](refl))
  }

  // =========================================================================
  // 2. Promonad Laws on Function
  // =========================================================================

  private val FunctionLaws = Promonad.FunctionIsPromonad.PromonadLaws

  test("Function is Promonad: unit naturality law") {
    val f1: Int => String     = i => if i >= 0 then s"pos:$i" else s"neg:$i"
    val h1: Double => Int     = d => math.round(d).toInt
    val k1: String => Boolean = _.startsWith("pos")
    val _                     = assert(FunctionLaws.unitNaturality(f1, h1, k1))

    val f2: Int => String     = _ => "const"
    val h2: Double => Int     = _ => 0
    val k2: String => Boolean = _ => false
    assert(FunctionLaws.unitNaturality(f2, h2, k2))
  }

  test("Function is Promonad: multiplication naturality law") {
    val h1: Double => Int  = d => math.floor(d).toInt
    val k1: Int => Boolean = _ > 0
    val _                  = assert(FunctionLaws.multiplicationNaturality[Int, String, Int, Double, Boolean](h1, k1))

    val h2: Double => Int  = _ => 1
    val k2: Int => Boolean = _ => true
    assert(FunctionLaws.multiplicationNaturality[Int, String, Int, Double, Boolean](h2, k2))
  }

  test("Function is Promonad: left identity law") {
    assert(FunctionLaws.leftIdentity[Int, String])
  }

  test("Function is Promonad: right identity law") {
    assert(FunctionLaws.rightIdentity[Int, String])
  }

  test("Function is Promonad: associativity law") {
    assert(FunctionLaws.associativity[Int, String, Double, Boolean])
  }

  test("Function is Promonad: coend wedge balancing law") {
    val f: Int => String = i => s"item:$i"
    assert(FunctionLaws.wedge[Double, String, Int, Boolean](f))
  }
}
