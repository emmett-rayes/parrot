package parrot
package category

class CategoryTest extends CategorySuite {

  // =========================================================================
  // 1. Category Laws on =:=
  // =========================================================================

  private val TypeEqLaws = Category.TypeEqIsCategory.CategoryLaws

  test("=:= is Category: left identity law") {
    val refl = summon[Int =:= Int]
    assert(TypeEqLaws.leftIdentity(refl))
  }

  test("=:= is Category: right identity law") {
    val refl = summon[Int =:= Int]
    assert(TypeEqLaws.rightIdentity(refl))
  }

  test("=:= is Category: associativity law") {
    val refl = summon[Int =:= Int]
    assert(TypeEqLaws.associativity(refl, refl, refl))
  }

  // =========================================================================
  // 2. Category Laws on Function
  // =========================================================================

  private val FunctionLaws = Category.FunctionIsCategory.CategoryLaws

  test("Function is Category: left identity law") {
    val f1: Int => String = i => if i >= 0 then s"+$i" else s"-$i"
    val f2: String => Int = _.length
    val _                 = assert(FunctionLaws.leftIdentity(f1))
    assert(FunctionLaws.leftIdentity(f2))
  }

  test("Function is Category: right identity law") {
    val f1: Int => String = i => if i >= 0 then s"+$i" else s"-$i"
    val f2: String => Int = _.length
    val _                 = assert(FunctionLaws.rightIdentity(f1))
    assert(FunctionLaws.rightIdentity(f2))
  }

  test("Function is Category: associativity law") {
    val f: Int => String     = i => if i >= 0 then s"+$i" else s"-$i"
    val g: String => Double  = _.length.toDouble
    val h: Double => Boolean = _ > 2.0
    assert(FunctionLaws.associativity(f, g, h))
  }

  // =========================================================================
  // 3. Category Laws on Promonad Underlying Category
  // =========================================================================

  private val PromonadCategoryLaws = Promonad.FunctionIsPromonad.PromonadIsCategory.CategoryLaws

  test("Promonad underlying category: left identity law") {
    val p: Unit => (Int => String) = _ => (i => if i >= 0 then s"+$i" else s"-$i")
    assert(PromonadCategoryLaws.leftIdentity(p))
  }

  test("Promonad underlying category: right identity law") {
    val p: Unit => (Int => String) = _ => (i => if i >= 0 then s"+$i" else s"-$i")
    assert(PromonadCategoryLaws.rightIdentity(p))
  }

  test("Promonad underlying category: associativity law") {
    val p: Unit => (Int => String)     = _ => (i => if i >= 0 then s"+$i" else s"-$i")
    val q: Unit => (String => Double)  = _ => (_.length.toDouble)
    val r: Unit => (Double => Boolean) = _ => (_ > 2.0)
    assert(PromonadCategoryLaws.associativity(p, q, r))
  }
}
