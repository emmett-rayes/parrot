package parrot
package category

import org.scalacheck.Gen

import Category.Type

/** Generators, variants and observations for the arrows of a promonad over a category whose objects are all types. */
abstract class PromonadFixture(
  val name: String,
  tracked val promonad: Promonad.On[Category { type Obj = Type }],
) extends caps.Pure {
  import promonad.P

  /** The fixture of the base category, for pure arrows. */
  val category: CategoryFixture.For[promonad.category.type]

  /** Generates arrows *X* → *Y*, including the cases that matter for the promonad (failure, effects). */
  def arrow[X: Sample, Y: Sample]: Gen[P[X, Y]]

  /** An arrow equal to *p* by construction, but a different value. */
  def variant[X: Sample, Y: Sample](p: P[X, Y]): P[X, Y]

  /** Observations of arrows *X* → *Y*, at sample points chosen afresh for every property. */
  def observe[X: Sample, Y: Sample]: Gen[P[X, Y] is Observable]

  /** Observations of functions between arrow types, at sample arrows chosen afresh for every property. */
  final def onArrows[X1: Sample, Y1: Sample, X2: Sample, Y2: Sample]: Gen[(P[X1, Y1] -> P[X2, Y2]) is Observable] = {
    for {
      arrows  <- Gen.listOfN(4, arrow[X1, Y1])
      observe <- observe[X2, Y2]
    } yield Observable.total[P[X1, Y1], P[X2, Y2]](arrows)(using observe)
  }

  /** The same generators, for the category of arrows. */
  final lazy val arrows: CategoryFixture.For[promonad.arrows.type] = PromonadFixture.Category(this)
}

/** The fixtures of promonads.
  *
  * A spec finds the fixture of the promonad it checks among these givens, so there is one per promonad.
  */
object PromonadFixture {

  /** The fixtures for a promonad *P*. */
  type For[P <: Promonad] = PromonadFixture { val promonad: P }

  /** `Kleisli[Option]`: functions that fail often enough for failure to matter. */
  given OptionKleisliIsFixture: For[Kleisli.OptionKleisli.type] = OptionKleisliFixture

  /** 𝒮 as a promonad over itself. */
  given ScalaFunctionsIsFixture: For[Total.Functions.type] = ScalaFunctionsFixture

  /** `Kleisli[Writer[String]]`. */
  given StringWriterKleisliIsFixture: For[StringWriterKleisli.type] = StringWriterKleisliFixture

  /** `Kleisli[State[String, Option]]`. */
  given StringStateKleisliIsFixture: For[StringStateKleisli.type] = StringStateFixture

  /** 𝒫 at its total programs, as a promonad over itself. */
  given PartialProgramsIsFixture: For[Partial.Programs.type] = PartialProgramsFixture

  /** 𝒫ᵒᵖ as a promonad over itself, at its total programs. */
  given PartialOpIsFixture: For[PartialFixedPoints.strong.profunctor.type] = PartialOpFixture

  /** The fixture of the category of arrows of a promonad. */
  final class Category(tracked val fixture: PromonadFixture)
      extends CategoryFixture(fixture.name, fixture.promonad.arrows) {
    import fixture.promonad.P

    def arrow[X: Sample, Y: Sample]: Gen[P[X, Y]] = {
      fixture.arrow[X, Y]
    }

    def variant[X: Sample, Y: Sample](p: P[X, Y]): P[X, Y] = {
      fixture.variant[X, Y](p)
    }

    def observe[X: Sample, Y: Sample]: Gen[P[X, Y] is Observable] = {
      fixture.observe[X, Y]
    }
  }
}

/** `Kleisli[Option]`: functions that fail often enough for failure to matter. */
object OptionKleisliFixture extends PromonadFixture("Kleisli[Option]", Kleisli.OptionKleisli) {
  val category: TotalFixture.type = TotalFixture

  def arrow[X: Sample, Y: Sample]: Gen[X -> Option[Y]] = {
    val results = Gen.frequency(1 -> Gen.const(None), 3 -> Y.gen.map(Some(_)))
    Gen.function1[X, Option[Y]](results)(using X.cogen)
  }

  def variant[X: Sample, Y: Sample](p: X -> Option[Y]): X -> Option[Y] = {
    x => p(x)
  }

  def observe[X: Sample, Y: Sample]: Gen[(X -> Option[Y]) is Observable] = {
    TotalFixture.observe[X, Option[Y]]
  }
}
