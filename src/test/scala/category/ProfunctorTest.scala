package parrot
package category

import org.scalacheck.{Arbitrary, Prop, Test}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

class ProfunctorTest extends AnyFunSuite with ScalaCheckPropertyChecks {

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

  given ArbitraryFunctionIsEq: [A: Arbitrary, B: Eq] => Function[A, B] is Eq {
    def eq(f: A => B, g: A => B): Boolean = {
      val prop = Prop.forAll((a: A) => f(a) === g(a))
      Test.check(Test.Parameters.default, prop).passed
    }
  }

  test("Function is Profunctor: identity law") {
    val p: Int => String = _.toString
    assert(FunctionLaws.identity(p))
  }

  test("Function is Profunctor: composition law") {
    val p: Int => String     = n => s"num:$n"
    val f1: Double => Int    = _.toInt
    val f2: String => Double = _.length.toDouble
    val g1: String => Int    = _.length
    val g2: Int => Boolean   = _ % 2 == 0
    assert(FunctionLaws.composition(p, f1, g1, f2, g2))
  }
}
