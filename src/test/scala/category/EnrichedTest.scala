package parrot
package category

import category.Enriched.over

import org.scalatest.funsuite.AnyFunSuite

class EnrichedTest extends AnyFunSuite {

  type OptionFunction = [A, B] =>> (A => Option[B])

  given OptionFunctionIsProfunctor: OptionFunction is Profunctor {
    type On = Function

    def dimap[A, B, C, D](f: C => A, g: B => D)(p: A => Option[B]): C => Option[D] = {
      c => p(f(c)).map(g)
    }
  }

  given OptionFunctionIsEnriched: (OptionFunction is Enriched) {
    type Over = Monoid.Additive

    override given HomIsV: [A, B] => ((A => Option[B]) is Monoid.Additive) = {
      Monoid.Additive.FunctionIsAdditive[A, Option[B]]
    }
  }

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
    val _ = assert(additive.plus(zeroFn, g)(0) == g(0))
  }

  test("Enriched summons via Enriched.apply") {
    val enriched = Enriched[OptionFunction]
    import enriched.given

    val evidence = summon[(Int => Option[String]) is enriched.V]
    val _        = assert(evidence.isInstanceOf[Monoid.Additive])
  }
}
