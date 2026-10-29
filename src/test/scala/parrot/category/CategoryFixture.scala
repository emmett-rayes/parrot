package parrot
package category

import org.scalacheck.Gen

/** Generators, variants and observations for the morphisms of a category whose objects are all types. */
abstract class CategoryFixture(val name: String, tracked val K: Category { type Obj = Type }) extends caps.Pure {
  import K.-->

  /** Generates morphisms *X* → *Y*, including the cases that matter for the category (failure, effects). */
  def arrow[X: Sample, Y: Sample]: Gen[X --> Y]

  /** A morphism equal to *f* by construction, but a different value. */
  def variant[X: Sample, Y: Sample](f: X --> Y): X --> Y

  /** Observations of morphisms *X* → *Y*, at sample points chosen afresh for every property. */
  def observe[X: Sample, Y: Sample]: Gen[(X --> Y) is Observable]
}

/** The fixtures of categories.
  *
  * A spec finds the fixture of the category it checks among these givens, so there is one per category.
  */
object CategoryFixture {

  /** A fixture for the category *C*. */
  type On[C <: Category] = CategoryFixture { val K: C }

  /** 𝒮: generated pure functions. */
  given TotalIsFixture: On[Total.type] = TotalFixture

  /** 𝒫, at its total morphisms. */
  given PartialIsFixture: On[Partial.type] = PartialFixture

  /** 𝒮ᵒᵖ: the functions of 𝒮, reversed. */
  given TotalOpIsFixture: On[Total.op.type] = OpFixture(TotalFixture)

  /** The category of arrows of `Kleisli[Option]`. */
  given OptionKleisliCategoryIsFixture: On[Kleisli.OptionKleisli.category.type] = OptionKleisliFixture.category

  /** The category of arrows of `Kleisli[Writer[String]]`. */
  given StringWriterKleisliCategoryIsFixture: On[StringWriterKleisli.category.type] = {
    StringWriterKleisliFixture.category
  }
}

/** [[CategoryFixture]] for the opposite of a category with a fixture.
  *
  * Morphisms *X* → *Y* in the opposite fixture correspond to morphisms *Y* → *X* in the original fixture.
  */
final class OpFixture(tracked val F: CategoryFixture) extends CategoryFixture(s"${F.name}ᵒᵖ", F.K.op) {
  import F.K.-->

  def arrow[X: Sample, Y: Sample]: Gen[Y --> X] = {
    F.arrow
  }

  def variant[X: Sample, Y: Sample](f: Y --> X): Y --> X = {
    F.variant(f)
  }

  def observe[X: Sample, Y: Sample]: Gen[(Y --> X) is Observable] = {
    F.observe
  }
}

/** [[CategoryFixture]] for [[Total]].
  *   - generates morphisms as pure functions
  *   - builds variants by η-expansion
  *   - observes morphisms by application to sample points
  */
object TotalFixture extends CategoryFixture("Total", Total) {

  def arrow[X: Sample, Y: Sample]: Gen[X -> Y] = {
    Sample.function
  }

  def variant[X: Sample, Y: Sample](f: X -> Y): X -> Y = {
    x => f(x)
  }

  def observe[X: Sample, Y: Sample]: Gen[(X -> Y) is Observable] = {
    Sample.points[X].map { points =>
      Observable.total(points)(using Observable.EqIsObservable(using Y.eq))
    }
  }
}

/** [[CategoryFixture]] for [[Partial]].
  *   - generates total morphisms as pure functions
  *   - builds variants by η-expansion
  *   - observes morphisms by application to sample points
  *
  * @note Divergence cannot be observed by a terminating test.
  */
object PartialFixture extends CategoryFixture("Partial", Partial) {

  def arrow[X: Sample, Y: Sample]: Gen[X ~> Y] = {
    Sample.function[X, Y].map(Partial.fromTotal(_))
  }

  def variant[X: Sample, Y: Sample](f: X ~> Y): X ~> Y = {
    Partial(x => f.run(x))
  }

  def observe[X: Sample, Y: Sample]: Gen[(X ~> Y) is Observable] = {
    Sample.points[X].map { points =>
      Observable.partial(points)(using Observable.EqIsObservable(using Y.eq))
    }
  }
}
