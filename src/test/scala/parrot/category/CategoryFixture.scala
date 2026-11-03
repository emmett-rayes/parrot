package parrot
package category

import org.scalacheck.Gen

import Category.Type

/** Generators, variants and observations for the morphisms of a category whose objects are all types. */
abstract class CategoryFixture(val name: String, tracked val category: Category { type Obj = Type }) extends caps.Pure {
  import category.-->

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

  /** The fixtures for a category **K**. */
  type For[K <: Category] = CategoryFixture { val category: K }

  /** 𝒮: generated pure functions. */
  given TotalIsFixture: For[Total.type] = TotalFixture

  /** 𝒫, at its total morphisms. */
  given PartialIsFixture: For[Partial.type] = PartialFixture

  /** 𝒮ᵒᵖ: the functions of 𝒮, reversed. */
  given TotalOpIsFixture: For[Total.op.type] = OpFixture(TotalFixture)

  /** 𝒫ᵒᵖ: the total morphisms of 𝒫, reversed. */
  given PartialOpIsFixture: For[Partial.op.type] = OpFixture(PartialFixture)

  /** The category of arrows of `Kleisli[Option]`. */
  given OptionKleisliCategoryIsFixture: For[Kleisli.OptionKleisli.arrows.type] = OptionKleisliFixture.arrows

  /** The category of arrows of `Kleisli[Writer[String]]`. */
  given StringWriterKleisliCategoryIsFixture: For[StringWriterKleisli.arrows.type] = {
    StringWriterKleisliFixture.arrows
  }
}

/** [[CategoryFixture]] for the opposite of a category with a fixture.
  *
  * Morphisms *X* → *Y* in the opposite fixture correspond to morphisms *Y* → *X* in the original fixture.
  */
final class OpFixture(tracked val fixture: CategoryFixture)
    extends CategoryFixture(s"${fixture.name}ᵒᵖ", fixture.category.op) {
  import fixture.category.-->

  def arrow[X: Sample, Y: Sample]: Gen[Y --> X] = {
    fixture.arrow
  }

  def variant[X: Sample, Y: Sample](f: Y --> X): Y --> X = {
    fixture.variant(f)
  }

  def observe[X: Sample, Y: Sample]: Gen[(Y --> X) is Observable] = {
    fixture.observe
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
