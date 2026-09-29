package parrot
package category

import org.scalacheck.{Arbitrary, Gen}

class EnrichedTest extends CategorySuite {

  // =========================================================================
  // 1. OptionFunction (Kleisli Category of Option)
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

  import OptionFunctionIsEnriched.given
  private val OptionFunctionLaws = OptionFunctionIsEnriched.MonoidEnrichedLaws

  test("OptionFunction is Enriched: unit homomorphy law") {
    val f1: String => Int    = _.length
    val g1: String => String = _ + "!"
    val _                    = assert(OptionFunctionLaws.unitHomomorphy(f1, g1))

    val f2: Int => Int    = _ * 2
    val g2: String => Int = _.length
    assert(OptionFunctionLaws.unitHomomorphy(f2, g2))
  }

  test("OptionFunction is Enriched: multiplication homomorphy law") {
    given Arbitrary[Int => Option[String]] = Arbitrary {
      Gen.oneOf(
        Gen.const((i: Int) => if i > 0 then Some(s"pos:$i") else None),
        Gen.const((i: Int) => if i < 0 then Some(s"neg:$i") else None),
        Gen.const((i: Int) => if i % 2 == 0 then Some(s"even:$i") else None),
        Gen.const((i: Int) => if i == 0 then Some("zero") else None),
        Gen.const((i: Int) => Some(s"all:$i")),
        Gen.const((_: Int) => None),
      )
    }

    val f1: String => Int    = _.length
    val g1: String => String = _ + "!"
    val _                    = assert(OptionFunctionLaws.multiplicationHomomorphy(f1, g1))

    val f2: Int => Int    = i => if i >= 0 then i else -i
    val g2: String => Int = _.length
    assert(OptionFunctionLaws.multiplicationHomomorphy(f2, g2))
  }

  test("OptionFunction is Enriched: right distributivity law") {
    given Arbitrary[String => Option[Boolean]] = Arbitrary {
      Gen.oneOf(
        Gen.const((s: String) => if s.nonEmpty then Some(true) else None),
        Gen.const((s: String) => if s.length > 3 then Some(false) else None),
        Gen.const((s: String) => if s.startsWith("pos") then Some(true) else None),
        Gen.const((s: String) => if s.startsWith("even") then Some(false) else None),
        Gen.const((_: String) => None),
        Gen.const((_: String) => Some(true)),
      )
    }

    val q1: OptionFunction[Int, String] = i => if i >= 0 then Some(i.toString) else None
    val q2: OptionFunction[Int, String] = i => if i % 2 == 0 then Some(s"even:$i") else None
    val q3: OptionFunction[Int, String] = _ => None
    val q4: OptionFunction[Int, String] = i => Some(s"all:$i")

    val _ = assert(OptionFunctionLaws.rightDistributivity(q1))
    val _ = assert(OptionFunctionLaws.rightDistributivity(q2))
    val _ = assert(OptionFunctionLaws.rightDistributivity(q3))
    assert(OptionFunctionLaws.rightDistributivity(q4))
  }

  test("OptionFunction is Enriched: left distributivity law on total and zero morphisms") {
    given Arbitrary[Int => Option[String]] = Arbitrary {
      Gen.oneOf(
        Gen.const((i: Int) => if i > 0 then Some(s"pos:$i") else None),
        Gen.const((i: Int) => if i < 0 then Some(s"neg:$i") else None),
        Gen.const((i: Int) => if i % 2 == 0 then Some(s"even:$i") else None),
        Gen.const((i: Int) => if i == 0 then Some("zero") else None),
        Gen.const((i: Int) => Some(s"all:$i")),
        Gen.const((_: Int) => None),
      )
    }

    val pTotal1: OptionFunction[String, Boolean] = OptionFunctionIsPromonad.unit(_.nonEmpty)
    val pTotal2: OptionFunction[String, Boolean] = OptionFunctionIsPromonad.unit(_.length > 3)
    val pZero: OptionFunction[String, Boolean]   = _ => None

    val _ = assert(OptionFunctionLaws.leftDistributivity(pTotal1))
    val _ = assert(OptionFunctionLaws.leftDistributivity(pTotal2))
    assert(OptionFunctionLaws.leftDistributivity(pZero))
  }

  test("OptionFunction is Enriched: unit annihilation law") {
    val p1: OptionFunction[String, Boolean] = s => Some(s.nonEmpty)
    val q1: OptionFunction[Int, String]     = i => Some(i.toString)
    val _                                   = assert(OptionFunctionLaws.unitAnnihilation(p1, q1))

    val p2: OptionFunction[String, Boolean] = _ => None
    val q2: OptionFunction[Int, String]     = i => if i > 0 then Some(s"$i") else None
    assert(OptionFunctionLaws.unitAnnihilation(p2, q2))
  }

  // =========================================================================
  // 2. RelFunction (Category of Relations / Non-Deterministic Computations)
  // =========================================================================

  type RelFunction = [A, B] =>> (A => Set[B])

  given RelFunctionIsPromonad: RelFunction is Promonad {
    type On = Function

    def unit[A, B](f: A => B): A => Set[B] = {
      a => Set(f(a))
    }

    def multiply[A, B, C](q: B => Set[C], p: A => Set[B]): A => Set[C] = {
      a => p(a).flatMap(q)
    }

    override def dimap[A, B, C, D](f: C => A, g: B => D)(p: A => Set[B]): C => Set[D] = {
      c => p(f(c)).map(g)
    }
  }

  given RelFunctionIsEnriched: RelFunction is Enriched {
    type Over = Monoid.Additive
    override val Prom: RelFunctionIsPromonad.type = summon

    override given HomIsV: [A, B] => ((A => Set[B]) is Monoid.Additive) = {
      Monoid.Additive.FunctionIsAdditive[A, Set[B]]
    }
  }

  import RelFunctionIsEnriched.given
  private val RelFunctionLaws = RelFunctionIsEnriched.MonoidEnrichedLaws

  test("RelFunction is Enriched: unit homomorphy law") {
    val f: String => Int    = _.length
    val g: String => String = _ + "!"
    assert(RelFunctionLaws.unitHomomorphy(f, g))
  }

  test("RelFunction is Enriched: multiplication homomorphy law") {
    given Arbitrary[Int => Set[String]] = Arbitrary {
      Gen.oneOf(
        Gen.const((i: Int) => if i > 0 then Set(s"pos:$i", s"val:$i") else Set.empty),
        Gen.const((i: Int) => if i % 2 == 0 then Set(s"even:$i") else Set(s"odd:$i")),
        Gen.const((i: Int) => Set(s"item:$i")),
        Gen.const((_: Int) => Set.empty[String]),
      )
    }

    val f: String => Int    = _.length
    val g: String => String = _ + "!"
    assert(RelFunctionLaws.multiplicationHomomorphy(f, g))
  }

  test("RelFunction is Enriched: right distributivity law") {
    given Arbitrary[String => Set[Boolean]] = Arbitrary {
      Gen.oneOf(
        Gen.const((s: String) => if s.nonEmpty then Set(true, false) else Set.empty),
        Gen.const((s: String) => if s.length > 3 then Set(false) else Set(true)),
        Gen.const((_: String) => Set.empty[Boolean]),
        Gen.const((_: String) => Set(true)),
      )
    }

    val q1: RelFunction[Int, String] = i => if i >= 0 then Set(i.toString, s"+$i") else Set.empty
    val q2: RelFunction[Int, String] = _ => Set.empty
    val _                            = assert(RelFunctionLaws.rightDistributivity(q1))
    assert(RelFunctionLaws.rightDistributivity(q2))
  }

  test("RelFunction is Enriched: unconditional left distributivity law") {
    given Arbitrary[Int => Set[String]] = Arbitrary {
      Gen.oneOf(
        Gen.const((i: Int) => if i > 0 then Set(s"pos:$i", s"val:$i") else Set.empty),
        Gen.const((i: Int) => if i % 2 == 0 then Set(s"even:$i") else Set(s"odd:$i")),
        Gen.const((i: Int) => Set(s"item:$i")),
        Gen.const((_: Int) => Set.empty[String]),
      )
    }

    val pPartial: RelFunction[String, Boolean] = s => if s.startsWith("pos") then Set(true) else Set.empty
    val pMulti: RelFunction[String, Boolean]   = s => Set(s.nonEmpty, s.length > 2)
    val pEmpty: RelFunction[String, Boolean]   = _ => Set.empty

    val _ = assert(RelFunctionLaws.leftDistributivity(pPartial))
    val _ = assert(RelFunctionLaws.leftDistributivity(pMulti))
    assert(RelFunctionLaws.leftDistributivity(pEmpty))
  }

  test("RelFunction is Enriched: unit annihilation law") {
    val p: RelFunction[String, Boolean] = s => if s.nonEmpty then Set(true) else Set.empty
    val q: RelFunction[Int, String]     = i => Set(i.toString)
    assert(RelFunctionLaws.unitAnnihilation(p, q))
  }
}
