package parrot
package category

import org.scalacheck.{Arbitrary, Gen, Prop, Test}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

class EnrichedTest extends AnyFunSuite with ScalaCheckPropertyChecks {

  // =========================================================================
  // Setup & Instances
  // =========================================================================

  type OptionFunction = [A, B] =>> (A => Option[B])

  given OptionFunctionIsPromonad: OptionFunction is Promonad {
    type On = Function

    def unit[A, B](f: A => B): A => Option[B] = {
      a => Some(f(a))
    }

    def multiply[A, B, C](q: B => Option[C], p: A => Option[B]): A => Option[C] = {
      a => p(a).flatMap(q)
    }

    override def dimap[A, B, C, D](f: C => A, g: B => D)(p: A => Option[B]): C => Option[D] = {
      c => p(f(c)).map(g)
    }
  }

  given OptionFunctionIsEnriched: OptionFunction is Enriched {
    type Over = Monoid.Additive
    override val Prom: OptionFunctionIsPromonad.type = summon

    override given HomIsV: [A, B] => ((A => Option[B]) is Monoid.Additive) = {
      Monoid.Additive.FunctionIsAdditive[A, Option[B]]
    }
  }

  given ArbitraryFunctionIsEq: [A: Arbitrary, B: Eq] => Function[A, B] is Eq {
    def eq(f: A => B, g: A => B): Boolean = {
      val prop = Prop.forAll((a: A) => f(a) === g(a))
      Test.check(Test.Parameters.default, prop).passed
    }
  }

  // =========================================================================
  // Monoid-Enriched Laws (Point-Free)
  // =========================================================================

  import OptionFunctionIsEnriched.given
  private val OptionFunctionMonoidEnrichedLaws = OptionFunctionIsEnriched.MonoidEnrichedLaws

  test("OptionFunction is Enriched: unit homomorphy law") {
    val f: String => Int    = _.length
    val g: String => String = _ + "!"

    assert(OptionFunctionMonoidEnrichedLaws.unitHomomorphy(f, g))
  }

  test("OptionFunction is Enriched: multiplication homomorphy law") {
    given Arbitrary[Int => Option[String]] = Arbitrary {
      Gen.oneOf(
        Gen.const((i: Int) => Some(s"val:$i")),
        Gen.const((i: Int) => if i > 0 then Some(s"pos:$i") else None),
        Gen.const((_: Int) => None),
      )
    }

    val f: String => Int    = _.length
    val g: String => String = _ + "!"

    assert(OptionFunctionMonoidEnrichedLaws.multiplicationHomomorphy(f, g))
  }

  test("OptionFunction is Enriched: right distributivity law") {
    given Arbitrary[String => Option[Boolean]] = Arbitrary {
      Gen.oneOf(
        Gen.const((s: String) => if s.nonEmpty then Some(true) else None),
        Gen.const((s: String) => if s.length > 3 then Some(false) else None),
        Gen.const((_: String) => None),
      )
    }

    val q: OptionFunction[Int, String] = i => if i >= 0 then Some(i.toString) else None

    assert(OptionFunctionMonoidEnrichedLaws.rightDistributivity(q))
  }

  test("OptionFunction is Enriched: left distributivity law") {
    given Arbitrary[Int => Option[String]] = Arbitrary {
      Gen.oneOf(
        Gen.const((i: Int) => if i > 0 then Some(s"pos:$i") else None),
        Gen.const((i: Int) => if i == 0 then Some("zero") else None),
        Gen.const((_: Int) => None),
      )
    }

    val p: OptionFunction[String, Boolean] = s => if s.nonEmpty then Some(true) else None

    assert(OptionFunctionMonoidEnrichedLaws.leftDistributivity(p))
  }

  test("OptionFunction is Enriched: unit annihilation law") {
    val p: OptionFunction[String, Boolean] = s => Some(s.nonEmpty)
    val q: OptionFunction[Int, String]     = i => Some(i.toString)

    assert(OptionFunctionMonoidEnrichedLaws.unitAnnihilation(p, q))
  }
}
