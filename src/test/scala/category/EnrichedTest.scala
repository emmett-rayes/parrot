package parrot
package category

import category.Enriched.over
import category.Monoid.in

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

    def unit[A, B](f: A => B): A => Option[B] = { a => Some(f(a)) }

    def multiply[A, B, C](q: B => Option[C], p: A => Option[B]): A => Option[C] = {
      a => p(a).flatMap(q)
    }

    override def dimap[A, B, C, D](f: C => A, g: B => D)(p: A => Option[B]): C => Option[D] = {
      c => p(f(c)).map(g)
    }
  }

  given OptionFunctionIsEnriched: OptionFunction is Enriched {
    type Over = Monoid.Additive

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

  private given [M] => (m: M is Monoid.Additive)
    => (M is (Monoid in Function) { val Mon: OptionFunctionMonoidEnrichedLaws.FMon.type }) =
    m.asInstanceOf[M is (Monoid in Function) { val Mon: OptionFunctionMonoidEnrichedLaws.FMon.type }]

  // =========================================================================
  // 1. Instance Summons
  // =========================================================================

  test("Enriched summons with 'over Monoid.Additive'") {
    val enriched = summon[OptionFunction is Enriched over Monoid.Additive]
    import enriched.given

    val f: Int => Option[String] = i => if i > 0 then Some(s"pos: $i") else None
    val g: Int => Option[String] = i => if i == 0 then Some("zero") else None

    val additive = summon[(Int => Option[String]) is Monoid.Additive]
    val zeroFn   = additive.zero
    val plusFn   = additive.plus(f, g)

    val _ = assert(plusFn(1) == Some("pos: 1"))
    val _ = assert(plusFn(0) == Some("zero"))
    val _ = assert(plusFn(-1) == None)
    val _ = assert(additive.plus(f, zeroFn)(1) == f(1))
    assert(additive.plus(zeroFn, g)(0) == g(0))
  }

  test("Enriched summons via Enriched.apply") {
    val enriched = Enriched[OptionFunction]
    import enriched.given

    val evidence = summon[(Int => Option[String]) is enriched.V]
    assert(evidence.isInstanceOf[Monoid.Additive])
  }

  // =========================================================================
  // 2. Monoid-Enriched Laws
  // =========================================================================

  private val OptionFunctionMonoidEnrichedLaws = OptionFunctionIsEnriched.MonoidEnrichedLaws

  test("OptionFunction is Enriched: unit homomorphy law") {
    given Arbitrary[OptionFunctionMonoidEnrichedLaws.FMon.I] =
      Arbitrary(Gen.const(().asInstanceOf[OptionFunctionMonoidEnrichedLaws.FMon.I]))

    val f: String => Int    = _.length
    val g: String => String = _ + "!"
    assert(OptionFunctionMonoidEnrichedLaws.unitHomomorphy(f, g))
  }

  test("OptionFunction is Enriched: multiplication homomorphy law") {
    type TensorPair = OptionFunctionMonoidEnrichedLaws.FMon.Tensor[Int => Option[String], Int => Option[String]]
    given Arbitrary[TensorPair] =
      Arbitrary.arbTuple2[Int => Option[String], Int => Option[String]].asInstanceOf[Arbitrary[TensorPair]]

    val f: String => Int    = _.length
    val g: String => String = _ + "!"
    assert(OptionFunctionMonoidEnrichedLaws.multiplicationHomomorphy(f, g))
  }
}
