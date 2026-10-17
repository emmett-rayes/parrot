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
    assert(TypeEqLaws.multiplicationNaturality(refl, refl, refl, refl))
  }

  test("=:= is Promonad: left identity law") {
    val refl = summon[Int =:= Int]
    assert(TypeEqLaws.leftIdentity(refl))
  }

  test("=:= is Promonad: right identity law") {
    val refl = summon[Int =:= Int]
    assert(TypeEqLaws.rightIdentity(refl))
  }

  test("=:= is Promonad: associativity law") {
    val refl = summon[Int =:= Int]
    assert(TypeEqLaws.associativity(refl, refl, refl))
  }

  test("=:= is Promonad: coend wedge balancing law") {
    val refl = summon[Int =:= Int]
    assert(TypeEqLaws.wedge(refl, refl, refl))
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
    val p1: Int => String  = i => if i % 2 == 0 then s"even:$i" else s"odd:$i"
    val q1: String => Int  = _.length
    val h1: Double => Int  = d => math.floor(d).toInt
    val k1: Int => Boolean = _ > 0
    val _                  = assert(FunctionLaws.multiplicationNaturality(p1, q1, h1, k1))

    val p2: Int => String  = _ => "fixed"
    val q2: String => Int  = _ => 42
    val h2: Double => Int  = _ => 1
    val k2: Int => Boolean = _ => true
    assert(FunctionLaws.multiplicationNaturality(p2, q2, h2, k2))
  }

  test("Function is Promonad: left identity law") {
    val p1: Int => String = i => if i >= 0 then s"pos:$i" else s"neg:$i"
    val p2: Int => String = _ => "const"
    val p3: String => Int = _.length
    val _                 = assert(FunctionLaws.leftIdentity(p1))
    val _                 = assert(FunctionLaws.leftIdentity(p2))
    assert(FunctionLaws.leftIdentity(p3))
  }

  test("Function is Promonad: right identity law") {
    val p1: Int => String = i => if i >= 0 then s"pos:$i" else s"neg:$i"
    val p2: Int => String = _ => "const"
    val p3: String => Int = _.length
    val _                 = assert(FunctionLaws.rightIdentity(p1))
    val _                 = assert(FunctionLaws.rightIdentity(p2))
    assert(FunctionLaws.rightIdentity(p3))
  }

  test("Function is Promonad: associativity law") {
    val p1: Int => String     = i => if i >= 0 then s"pos:$i" else s"neg:$i"
    val q1: String => Double  = _.length.toDouble
    val r1: Double => Boolean = _ > 3.0
    val _                     = assert(FunctionLaws.associativity(p1, q1, r1))

    val p2: Int => String     = _ => "const"
    val q2: String => Double  = _ => 10.0
    val r2: Double => Boolean = _ => true
    assert(FunctionLaws.associativity(p2, q2, r2))
  }

  test("Function is Promonad: coend wedge balancing law") {
    val q: String => Boolean = _.length > 3
    val f: Int => String     = i => s"item:$i"
    val p: Double => Int     = d => math.round(d).toInt
    val _                    = assert(FunctionLaws.wedge(q, f, p))

    val qBranch: String => Int  = s => if s.startsWith("p") then 1 else -1
    val fBranch: Int => String  = i => if i >= 0 then s"p:$i" else s"n:$i"
    val pBranch: Boolean => Int = if _ then 10 else -10
    assert(FunctionLaws.wedge(qBranch, fBranch, pBranch))
  }
}
