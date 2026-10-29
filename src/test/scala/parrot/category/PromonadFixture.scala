package parrot
package category

import org.scalacheck.Gen

/** Generators, variants and observations for the arrows of a promonad over a category whose objects are all types. */
abstract class PromonadFixture(val name: String, tracked val P: Promonad { val K: Category { type Obj = Type } })
    extends caps.Pure {
  import P.P

  /** The fixture of the base category, for pure arrows. */
  val base: CategoryFixture.On[P.K.type]

  /** Generates arrows *X* → *Y*, including the cases that matter for the promonad (failure, effects). */
  def arrow[X: Sample, Y: Sample]: Gen[P[X, Y]]

  /** An arrow equal to *p* by construction, but a different value. */
  def variant[X: Sample, Y: Sample](p: P[X, Y]): P[X, Y]

  /** Observations of arrows *X* → *Y*, at sample points chosen afresh for every property. */
  def observe[X: Sample, Y: Sample]: Gen[P[X, Y] is Observable]

  /** The same generators, for the category of arrows. */
  final lazy val category: CategoryFixture.On[P.category.type] = PromonadFixture.Category(this)
}

/** The fixtures of promonads.
  *
  * A spec finds the fixture of the promonad it checks among these givens, so there is one per promonad.
  */
object PromonadFixture {

  /** A fixture for the promonad *Q*. */
  type On[Q <: Promonad] = PromonadFixture { val P: Q }

  /** `Kleisli[Option]`: functions that fail often enough for failure to matter. */
  given OptionKleisliIsFixture: On[Kleisli.OptionKleisli.type] = OptionKleisliFixture

  /** 𝒮 as a promonad over itself. */
  given ScalaFunctionsIsFixture: On[Total.Functions.type] = ScalaFunctionsFixture

  /** `Kleisli[Writer[String]]`. */
  given StringWriterKleisliIsFixture: On[StringWriterKleisli.type] = StringWriterKleisliFixture

  /** `Kleisli[State[String, Option]]`. */
  given StringStateKleisliIsFixture: On[StringStateKleisli.type] = StringStateFixture

  /** 𝒫 at its total programs, as a promonad over itself. */
  given PartialProgramsIsFixture: On[Partial.Programs.type] = PartialProgramsFixture

  /** 𝒫ᵒᵖ as a promonad over itself, at its total programs. */
  given PartialOpIsFixture: On[PartialFixedPoints.S.P.type] = PartialOpFixture

  /** The fixture of the category of arrows of a promonad. */
  final class Category(tracked val F: PromonadFixture) extends CategoryFixture(F.name, F.P.category) {
    import F.P.P

    def arrow[X: Sample, Y: Sample]: Gen[P[X, Y]] = {
      F.arrow[X, Y]
    }

    def variant[X: Sample, Y: Sample](p: P[X, Y]): P[X, Y] = {
      F.variant[X, Y](p)
    }

    def observe[X: Sample, Y: Sample]: Gen[P[X, Y] is Observable] = {
      F.observe[X, Y]
    }
  }
}

/** `Kleisli[Option]`: functions that fail often enough for failure to matter. */
object OptionKleisliFixture extends PromonadFixture("Kleisli[Option]", Kleisli.OptionKleisli) {
  val base: TotalFixture.type = TotalFixture

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
