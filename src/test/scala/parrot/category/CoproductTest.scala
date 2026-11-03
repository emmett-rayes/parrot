package parrot
package category

import Category.Type

/** The laws of [[Coproducts]], for binary coproducts on a category whose objects are all types. */
abstract class CoproductsSpec(
  tracked override val category: Category { type Obj = Type },
  tracked override val bifunctor: Coproducts.On[category.type],
)(using
  fixture: CategoryFixture.For[category.type],
  typename: TypeName[bifunctor.Self],
  types: SampleTypes,
  sample: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[bifunctor.F[X, Y]],
) extends BifunctorSpec(category, bifunctor, "Coproducts") {
  import types.{T1, T2, T3, T4, given}
  import fixture.*
  import category.-->
  import bifunctor.F
  import bifunctor.CoproductsLaws.*

  private given BSample: [X: Sample, Y: Sample] => Sample[F[X, Y]] = sample[X, Y]

  also("Coproducts") {
    law("copairInl") {
      val observations = observe[T1, T4]
      val fs           = arrow[T1, T4]
      val gs           = arrow[T2, T4]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((T1 --> T4) is Observable) = observe
        copairInl(f, g)
      }
    }

    law("copairInr") {
      val observations = observe[T2, T4]
      val fs           = arrow[T1, T4]
      val gs           = arrow[T2, T4]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((T2 --> T4) is Observable) = observe
        copairInr(f, g)
      }
    }

    law("copairUniqueness") {
      val observations = observe[F[T1, T2], T4]
      val hs           = arrow[F[T1, T2], T4]

      forAll(observations, hs) { (observe, h) =>
        given ((F[T1, T2] --> T4) is Observable) = observe
        copairUniqueness[T1, T2, T4](h)
      }
    }

    law("copairCongruence") {
      val observations = observe[F[T1, T2], T4]
      val fs           = arrow[T1, T4]
      val gs           = arrow[T2, T4]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((F[T1, T2] --> T4) is Observable) = observe
        copairCongruence(f, variant(f), g, variant(g))
      }
    }

    law("bimapIsCopairing") {
      val observations = observe[F[T1, T2], F[T4, T3]]
      val fs           = arrow[T1, T4]
      val gs           = arrow[T2, T3]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((F[T1, T2] --> F[T4, T3]) is Observable) = observe
        bimapIsCopairing(f, g)
      }
    }
  }
}

class ScalaEitherIsCoproductsTest   extends CoproductsSpec(Total, Total.EitherIsCoproducts)
class PartialEitherIsCoproductsTest extends CoproductsSpec(Partial, Partial.EitherIsCoproducts)
class TotalColimitIsCoproductsTest  extends CoproductsSpec(Total, ColimitCoproducts)
