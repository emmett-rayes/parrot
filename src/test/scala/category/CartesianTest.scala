package parrot
package category

import org.scalacheck.{Arbitrary, Prop, Test}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

class CartesianTest extends AnyFunSuite with ScalaCheckPropertyChecks {

  // =========================================================================
  // Cartesian Laws on Function
  // =========================================================================

  private val FunctionLaws = Cartesian.FunctionIsCartesian.CartesianLaws

  given ArbitraryFunctionIsEq: [A: Arbitrary, B: Eq] => Function[A, B] is Eq {
    def eq(f: A => B, g: A => B): Boolean = {
      val prop = Prop.forAll((a: A) => f(a) === g(a))
      Test.check(Test.Parameters.default, prop).passed
    }
  }

  test("Function is Cartesian: first projection law") {
    val f: Int => String  = _.toString
    val g: Int => Boolean = _ > 0
    assert(FunctionLaws.firstProjection(f, g))
  }

  test("Function is Cartesian: second projection law") {
    val f: Int => String  = _.toString
    val g: Int => Boolean = _ > 0
    assert(FunctionLaws.secondProjection(f, g))
  }

  test("Function is Cartesian: product uniqueness law") {
    assert(FunctionLaws.productUniqueness[Int, String])
  }

  test("Function is Cartesian: terminal uniqueness law") {
    val f: Int => Unit = _ => ()
    assert(FunctionLaws.terminalUniqueness(f))
  }
}
