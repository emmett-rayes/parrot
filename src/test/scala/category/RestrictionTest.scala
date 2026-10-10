package parrot
package category

class RestrictionTest extends CategorySuite {

  // =========================================================================
  // 1. Restriction on Function
  // =========================================================================

  private val FunctionInstance = Restriction.FunctionIsRestriction
  private val FunctionLaws     = FunctionInstance.RestrictionLaws

  test("Function is Restriction: every morphism is total") {
    val p: Int => String = i => s"val:$i"
    val r                = FunctionInstance.restrict(p)
    assert(r(-3) == -3 && r(0) == 0 && r(42) == 42)
  }

  test("Function is Restriction satisfies restrictionIdentity law (R1)") {
    val p: Int => String = i => if i >= 0 then s"pos:$i" else s"neg:$i"
    assert(FunctionLaws.restrictionIdentity(p))
  }

  test("Function is Restriction satisfies restrictionCommutativity law (R2)") {
    val p: Int => String  = i => s"val:$i"
    val q: Int => Boolean = _ % 2 == 0
    assert(FunctionLaws.restrictionCommutativity(p, q))
  }

  test("Function is Restriction satisfies restrictionCompose law (R3)") {
    val p: Int => String  = i => s"val:$i"
    val q: Int => Boolean = _ % 2 == 0
    assert(FunctionLaws.restrictionCompose(p, q))
  }

  test("Function is Restriction satisfies restrictionPrecompose law (R4)") {
    val p: Int => String     = i => s"val:$i"
    val q: String => Boolean = _.length > 5
    assert(FunctionLaws.restrictionPrecompose(p, q))
  }

  // =========================================================================
  // 2. Restriction on PartialFunction
  // =========================================================================

  private val PartialInstance = Restriction.PartialFunctionIsRestriction
  private val PartialLaws     = PartialInstance.RestrictionLaws

  private val positive: PartialFunction[Int, String] = {
    case i if i > 0 => s"pos:$i"
  }

  private val even: PartialFunction[Int, Boolean] = {
    case i if i % 2 == 0 => i % 4 == 0
  }

  private val shortString: PartialFunction[String, Int] = {
    case s if s.length < 6 => s.length
  }

  test("PartialFunction is Restriction: restriction is the partial identity on the domain") {
    val r = PartialInstance.restrict(positive)
    assert(r.isDefinedAt(5) && !r.isDefinedAt(0) && !r.isDefinedAt(-5) && r(5) == 5)
  }

  test("PartialFunction is Restriction: unit is total") {
    val f: Int => String = i => s"val:$i"
    val promonad         = PartialInstance.SelfIsPromonad
    assert(PartialInstance.restrict(promonad.unit(f)) === promonad.identity[Int])
  }

  test("PartialFunction is Restriction: composition restricts the domain") {
    val composed = PartialInstance.SelfIsPromonad.andThen(positive, shortString)
    assert(composed.isDefinedAt(9) && !composed.isDefinedAt(10) && !composed.isDefinedAt(-1))
  }

  test("PartialFunction is Restriction satisfies PromonadLaws") {
    val laws = PartialInstance.SelfIsPromonad.PromonadLaws
    val _    = assert(laws.leftIdentity(positive))
    val _    = assert(laws.rightIdentity(positive))
    assert(laws.associativity(even, PartialFunction.fromFunction((b: Boolean) => b.toString), shortString))
  }

  test("PartialFunction is Restriction satisfies restrictionIdentity law (R1)") {
    val _ = assert(PartialLaws.restrictionIdentity(positive))
    assert(PartialLaws.restrictionIdentity(even))
  }

  test("PartialFunction is Restriction satisfies restrictionCommutativity law (R2)") {
    assert(PartialLaws.restrictionCommutativity(positive, even))
  }

  test("PartialFunction is Restriction satisfies restrictionCompose law (R3)") {
    val _ = assert(PartialLaws.restrictionCompose(positive, even))
    assert(PartialLaws.restrictionCompose(even, positive))
  }

  test("PartialFunction is Restriction satisfies restrictionPrecompose law (R4)") {
    assert(PartialLaws.restrictionPrecompose(positive, shortString))
  }
}
