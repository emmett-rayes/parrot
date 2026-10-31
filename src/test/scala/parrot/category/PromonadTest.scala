package parrot
package category

import org.scalacheck.Gen

import Sample.given

/** The laws of [[Promonad]] beyond those of its category: the unit is a functor, and the derived profunctor action
  * satisfies the [[Bifunctor]] laws.
  */
abstract class PromonadSpec(tracked val P: Promonad { val K: Category { type Obj = Type } })(
  using
  promonad: PromonadFixture.On[P.type],
  types: SampleTypes,
) extends LawSuite("Promonad", promonad.name) {
  import types.{T1, T2, T3, T4, given}
  import promonad.*
  import P.P
  import P.PromonadLaws.*

  /** Observes functions between arrow types at sample arrows. */
  private def onArrows[X1: Sample, Y1: Sample, X2: Sample, Y2: Sample]
    : Gen[(P[X1, Y1] -> P[X2, Y2]) is Observable] = {
    for {
      arrows  <- Gen.listOfN(4, arrow[X1, Y1])
      observe <- observe[X2, Y2]
    } yield Observable.through[P[X1, Y1] -> P[X2, Y2], P[X2, Y2]](arrows.map(p => h => h(p)))(
      using observe
    )
  }

  law("unitComposition") {
    val observations = observe[T1, T4]
    val fs           = base.arrow[T1, T2]
    val gs           = base.arrow[T2, T4]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given (P[T1, T4] is Observable) = observe
      unitComposition(f, g)
    }
  }

  law("unitCongruence") {
    val observations = observe[T1, T2]
    val fs           = base.arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given (P[T1, T2] is Observable) = observe
      unitCongruence(f, base.variant(f))
    }
  }

  also("Profunctor") {
    import P.BifunctorLaws.*

    law("identity") {
      forAll(onArrows[T1, T2, T1, T2]) { observe =>
        given ((P[T1, T2] -> P[T1, T2]) is Observable) = observe
        identity[T1, T2]
      }
    }

    law("composition") {
      forAll(
        onArrows[T1, T2, T4, T3],
        Gen.zip(base.arrow[T3, T1], base.arrow[T2, T1]),
        Gen.zip(base.arrow[T4, T3], base.arrow[T1, T3]),
      ) { case (observe, (f1, g1), (f2, g2)) =>
        given ((P[T1, T2] -> P[T4, T3]) is Observable) = observe
        composition[T1, T2, T3, T1, T4, T3](f1, g1, f2, g2)
      }
    }

    law("congruence") {
      val fs = base.arrow[T4, T1]
      val gs = base.arrow[T2, T3]

      forAll(onArrows[T1, T2, T4, T3], fs, gs) { (observe, f, g) =>
        given ((P[T1, T2] -> P[T4, T3]) is Observable) = observe
        congruence[T1, T2, T4, T3](f, base.variant(f), g, base.variant(g))
      }
    }
  }
}

/** 𝒮 as a promonad over itself. */
object ScalaFunctionsFixture extends PromonadFixture("Total", Total.Functions) {
  val base: TotalFixture.type = TotalFixture

  def arrow[X: Sample, Y: Sample]: Gen[X -> Y] = TotalFixture.arrow[X, Y]

  def variant[X: Sample, Y: Sample](p: X -> Y): X -> Y = TotalFixture.variant(p)

  def observe[X: Sample, Y: Sample]: Gen[(X -> Y) is Observable] = TotalFixture.observe[X, Y]
}

/** The Kleisli promonad of the string writer. */
object StringWriterKleisli extends Kleisli(StringWriter)

/** `Kleisli[Writer[String]]`: arrows that log. */
object StringWriterKleisliFixture extends PromonadFixture("Kleisli[Writer[String]]", StringWriterKleisli) {
  val base: TotalFixture.type = TotalFixture

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
class StringWriterKleisliIsPromonadTest extends PromonadSpec(StringWriterKleisli)
class StringWriterKleisliIsCategoryTest extends CategorySpec(StringWriterKleisli.category)
