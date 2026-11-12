package parrot
package category

import Sample.given
import Category.Type

/** The laws of [[Natural]], for transformations between functors on categories whose objects are all types.
  *
  * Arrows come from the fixture of the source category, observations from the fixture of the target category.
  */
abstract class NaturalSpec(
  name: String,
  tracked val natural: Natural.From[Functor.Into[Category { type Obj = Type }] {
    val source: Category { type Obj = Type }
  }],
)(using
  source: CategoryFixture.For[natural.functor1.source.type],
  target: CategoryFixture.For[natural.functor1.target.type],
  types: SampleTypes,
  sample1: [X] => Sample[X] ?-> Sample[natural.functor1.F[X]],
  sample2: [X] => Sample[X] ?-> Sample[natural.functor2.F[X]],
) extends LawSuite("Natural", name) {
  import types.{T1, T2, given}
  import source.arrow
  import target.observe
  import natural.functor1.F
  import natural.functor2.F as G
  import natural.functor1.target.--> as ==>
  import natural.NaturalLaws.*

  private given FSample: [X: Sample] => Sample[F[X]] = sample1[X]
  private given GSample: [X: Sample] => Sample[G[X]] = sample2[X]

  law("naturality") {
    val observations = observe[F[T1], G[T2]]
    val fs           = arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given ((F[T1] ==> G[T2]) is Observable) = observe
      naturality(f)
    }
  }
}

/** The functor `Option` ∘ `Option` on 𝒮. */
object OptionOption extends Functor.Composite(Monad.OptionIsMonad.functor, Monad.OptionIsMonad.functor)

/** The identity functor on 𝒮, by the generic construction. */
object TotalIdentity extends Endofunctor.Identity(Total)

class OptionUnitIsNaturalTest    extends NaturalSpec("Unit of Option", Monad.OptionIsMonad.unitIsNatural)
class OptionFlattenIsNaturalTest extends NaturalSpec("Multiplication of Option", Monad.OptionIsMonad.flattenIsNatural)
