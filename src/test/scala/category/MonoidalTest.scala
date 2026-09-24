package parrot
package category

import org.scalacheck.{Arbitrary, Prop, Test}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

class MonoidalTest extends AnyFunSuite with ScalaCheckPropertyChecks {

  // =========================================================================
  // Monoidal Laws on Function
  // =========================================================================

  private val FunctionLaws = Monoidal.FunctionIsMonoidal.MonoidalLaws

  given ArbitraryFunctionIsEq: [A: Arbitrary, B: Eq] => Function[A, B] is Eq {
    def eq(f: A => B, g: A => B): Boolean = {
      val prop = Prop.forAll((a: A) => f(a) === g(a))
      Test.check(Test.Parameters.default, prop).passed
    }
  }

  test("Function is Monoidal: tensor identity law") {
    assert(FunctionLaws.tensorIdentity[Int, String])
  }

  test("Function is Monoidal: tensor composition law") {
    val f1: Int => String     = _.toString
    val f2: String => Boolean = _.nonEmpty
    val g1: Double => Int     = _.toInt
    val g2: Int => String     = n => s"num:$n"
    assert(FunctionLaws.tensorComposition(f1, f2, g1, g2))
  }

  test("Function is Monoidal: associator naturality law") {
    val f: Int => String     = _.toString
    val g: Boolean => Int    = if _ then 1 else 0
    val h: Double => Boolean = _ > 0.0
    assert(FunctionLaws.associatorNaturality(f, g, h))
  }

  test("Function is Monoidal: left unitor naturality law") {
    val f: Int => String = _.toString
    assert(FunctionLaws.leftUnitorNaturality(f))
  }

  test("Function is Monoidal: right unitor naturality law") {
    val f: Int => String = _.toString
    assert(FunctionLaws.rightUnitorNaturality(f))
  }

  test("Function is Monoidal: triangle law") {
    assert(FunctionLaws.triangle[Int, String])
  }

  test("Function is Monoidal: pentagon law") {
    assert(FunctionLaws.pentagon[Int, String, Boolean, Double])
  }
}
