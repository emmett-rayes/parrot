package parrot
package category

import org.scalacheck.*

class ProfunctorTest extends CategorySuite {

  // =========================================================================
  // 1. Profunctor Laws on `=:=`
  // =========================================================================

  private val TypeEqLaws = Profunctor.TypeEqIsProfunctor.ProfunctorLaws

  test("=:= is Profunctor: identity law") {
    forAll { (A: ArbitraryType) =>
      assert(TypeEqLaws.identity[A.T, A.T])
    }
  }

  test("=:= is Profunctor: composition law") {
    forAll { (A: ArbitraryType) =>
      val refl = summon[A.T =:= A.T]
      assert(TypeEqLaws.composition(refl, refl, refl, refl))
    }
  }

  // =========================================================================
  // 2. Profunctor Laws on Function
  // =========================================================================

  private val FunctionLaws = Profunctor.FunctionIsProfunctor.ProfunctorLaws

  test("Function is Profunctor: identity law") {
    forAll { (A: ArbitraryType, B: ArbitraryType) =>
      assert(FunctionLaws.identity[A.T, B.T])
    }
  }

  test("Function is Profunctor: composition law") {
    forAll {
      (A: ArbitraryType, B: ArbitraryType, C: ArbitraryType, D: ArbitraryType, E: ArbitraryType, F: ArbitraryType) =>
        forAll { (f1: C.T -> A.T, g1: B.T -> D.T, f2: E.T -> C.T, g2: D.T -> F.T) =>
          assert(FunctionLaws.composition(f1, g1, f2, g2))
        }
    }
  }

  // =========================================================================
  // 3. Profunctor Laws on PureFunction
  // =========================================================================

  private val PureFunctionLaws = PureFunction.PureFunctionIsProfunctor.ProfunctorLaws

  test("PureFunctionL is Profunctor: identity law") {
    forAll { (A: ArbitraryType, B: ArbitraryType) =>
      assert(PureFunctionLaws.identity[A.T, B.T])
    }
  }

  test("PureFunction is Profunctor: composition law") {
    forAll {
      (A: ArbitraryType, B: ArbitraryType, C: ArbitraryType, D: ArbitraryType, E: ArbitraryType, F: ArbitraryType) =>
        forAll { (f1: C.T -> A.T, g1: B.T -> D.T, f2: E.T -> C.T, g2: D.T -> F.T) =>
          assert(PureFunctionLaws.composition(f1, g1, f2, g2))
        }
    }
  }
}
