package parrot
package category

import org.scalacheck.{Arbitrary, Prop, Test}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

class SymmetricTest extends AnyFunSuite with ScalaCheckPropertyChecks {

  // =========================================================================
  // Symmetric Laws on Function
  // =========================================================================

  private val FunctionLaws = Symmetric.FunctionIsSymmetric.SymmetricLaws

  given ArbitraryFunctionIsEq: [A: Arbitrary, B: Eq] => Function[A, B] is Eq {
    def eq(f: A => B, g: A => B): Boolean = {
      val prop = Prop.forAll((a: A) => f(a) === g(a))
      Test.check(Test.Parameters.default, prop).passed
    }
  }

  test("Function is Symmetric: braid naturality law") {
    val f: Int => String     = _.toString
    val g: Boolean => Double = if _ then 1.0 else 0.0
    assert(FunctionLaws.braidNaturality(f, g))
  }

  test("Function is Symmetric: symmetry law") {
    assert(FunctionLaws.symmetry[Int, String])
  }

  test("Function is Symmetric: hexagon law") {
    assert(FunctionLaws.hexagon[Int, String, Boolean])
  }
}
