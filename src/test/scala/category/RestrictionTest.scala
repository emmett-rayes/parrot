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
}
