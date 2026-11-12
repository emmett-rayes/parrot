package parrot
package category

import org.scalacheck.Gen

import Sample.given
import Category.Type

/** The laws of [[Promonad]] beyond those of its category: the unit is a functor, and the derived profunctor action
  * satisfies the [[Bifunctor]] laws.
  */
abstract class PromonadSpec(tracked val promonad: Promonad.On[Category { type Obj = Type }])(
  using
  fixture: PromonadFixture.For[promonad.type],
  types: SampleTypes,
) extends LawSuite("Promonad", fixture.name) {
  import types.{T1, T2, T3, T4, given}
  import fixture.*
  import promonad.P
  import promonad.PromonadLaws.*

  law("unitComposition") {
    val observations = observe[T1, T4]
    val fs           = category.arrow[T1, T2]
    val gs           = category.arrow[T2, T4]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given (P[T1, T4] is Observable) = observe
      unitComposition(f, g)
    }
  }

  law("unitCongruence") {
    val observations = observe[T1, T2]
    val fs           = category.arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given (P[T1, T2] is Observable) = observe
      unitCongruence(f, category.variant(f))
    }
  }

  law("identityIsUnit") {
    val observations = observe[T1, T1]

    forAll(observations) { observe =>
      given (P[T1, T1] is Observable) = observe
      identityIsUnit[T1]
    }
  }

  law("bimapDefinition") {
    val fs = category.arrow[T4, T1]
    val gs = category.arrow[T2, T3]

    forAll(onArrows[T1, T2, T4, T3], fs, gs) { (observe, f, g) =>
      given ((P[T1, T2] -> P[T4, T3]) is Observable) = observe
      bimapDefinition[T1, T2, T4, T3](f, g)
    }
  }

  also("Profunctor") {
    import promonad.BifunctorLaws.*

    law("identity") {
      forAll(onArrows[T1, T2, T1, T2]) { observe =>
        given ((P[T1, T2] -> P[T1, T2]) is Observable) = observe
        identity[T1, T2]
      }
    }

    law("composition") {
      forAll(
        onArrows[T1, T2, T4, T3],
        Gen.zip(category.arrow[T3, T1], category.arrow[T2, T1]),
        Gen.zip(category.arrow[T4, T3], category.arrow[T1, T3]),
      ) { case (observe, (f1, g1), (f2, g2)) =>
        given ((P[T1, T2] -> P[T4, T3]) is Observable) = observe
        composition[T1, T2, T3, T1, T4, T3](f1, g1, f2, g2)
      }
    }

    law("congruence") {
      val fs = category.arrow[T4, T1]
      val gs = category.arrow[T2, T3]

      forAll(onArrows[T1, T2, T4, T3], fs, gs) { (observe, f, g) =>
        given ((P[T1, T2] -> P[T4, T3]) is Observable) = observe
        congruence[T1, T2, T4, T3](f, category.variant(f), g, category.variant(g))
      }
    }

    law("lmapIsBimap") {
      val fs = category.arrow[T4, T1]

      forAll(onArrows[T1, T2, T4, T2], fs) { (observe, f) =>
        given ((P[T1, T2] -> P[T4, T2]) is Observable) = observe
        lmapIsBimap[T1, T4, T2](f)
      }
    }

    law("rmapIsBimap") {
      val gs = category.arrow[T2, T3]

      forAll(onArrows[T1, T2, T1, T3], gs) { (observe, g) =>
        given ((P[T1, T2] -> P[T1, T3]) is Observable) = observe
        rmapIsBimap[T2, T3, T1](g)
      }
    }
  }
}

/** 𝒮 as a promonad over itself. */
object ScalaFunctionsFixture extends PromonadFixture("Total", Total.Functions) {
  val category: TotalFixture.type = TotalFixture

  def arrow[X: Sample, Y: Sample]: Gen[X -> Y] = TotalFixture.arrow[X, Y]

  def variant[X: Sample, Y: Sample](p: X -> Y): X -> Y = TotalFixture.variant(p)

  def observe[X: Sample, Y: Sample]: Gen[(X -> Y) is Observable] = TotalFixture.observe[X, Y]
}

/** The Kleisli promonad of the string writer. */
object StringWriterKleisli extends Kleisli(StringWriter)

/** `Kleisli[Writer[String]]`: arrows that log. */
object StringWriterKleisliFixture extends PromonadFixture("Kleisli[Writer[String]]", StringWriterKleisli) {
  val category: TotalFixture.type = TotalFixture

  def arrow[X: Sample, Y: Sample]: Gen[X -> (String, Y)] = {
    val logs = Gen.oneOf("", "a", "b", "ab")
    Gen.function1[X, (String, Y)](Gen.zip(logs, Y.gen))(using X.cogen)
  }

  def variant[X: Sample, Y: Sample](p: X -> (String, Y)): X -> (String, Y) = {
    x => p(x)
  }

  def observe[X: Sample, Y: Sample]: Gen[(X -> (String, Y)) is Observable] = {
    TotalFixture.observe[X, (String, Y)]
  }
}

class OptionKleisliIsPromonadTest       extends PromonadSpec(Kleisli.OptionKleisli)
class ScalaFunctionsIsPromonadTest      extends PromonadSpec(Total.Functions)
class PartialProgramsIsPromonadTest     extends PromonadSpec(Partial.Programs)
class PartialComputationsIsPromonadTest extends PromonadSpec(Partial.Computations)
class StringWriterKleisliIsPromonadTest extends PromonadSpec(StringWriterKleisli)
class StringWriterKleisliIsCategoryTest extends CategorySpec(StringWriterKleisli.arrows)
