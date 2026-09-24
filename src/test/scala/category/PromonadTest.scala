package parrot
package category

import org.scalacheck.{Arbitrary, Prop, Test}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

class PromonadTest extends AnyFunSuite with ScalaCheckPropertyChecks {

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

  // =========================================================================
  // 2. Promonad Laws on Function
  // =========================================================================

  private val FunctionLaws = Promonad.FunctionIsPromonad.PromonadLaws

  given ArbitraryFunctionIsEq: [A: Arbitrary, B: Eq] => Function[A, B] is Eq {
    def eq(f: A => B, g: A => B): Boolean = {
      val prop = Prop.forAll((a: A) => f(a) === g(a))
      Test.check(Test.Parameters.default, prop).passed
    }
  }

  test("Function is Promonad: unit naturality law") {
    val f: Int => String     = _.toString
    val h: Double => Int     = _.toInt
    val k: String => Boolean = _.nonEmpty
    assert(FunctionLaws.unitNaturality(f, h, k))
  }

  test("Function is Promonad: multiplication naturality law") {
    val p: Int => String  = _.toString
    val q: String => Int  = _.length
    val h: Double => Int  = _.toInt
    val k: Int => Boolean = _ > 0
    assert(FunctionLaws.multiplicationNaturality(p, q, h, k))
  }

  test("Function is Promonad: left identity law") {
    val p: Int => String = _.toString
    assert(FunctionLaws.leftIdentity(p))
  }

  test("Function is Promonad: right identity law") {
    val p: Int => String = _.toString
    assert(FunctionLaws.rightIdentity(p))
  }

  test("Function is Promonad: associativity law") {
    val p: Int => String     = _.toString
    val q: String => Double  = _.length.toDouble
    val r: Double => Boolean = _ > 0
    assert(FunctionLaws.associativity(p, q, r))
  }
}
