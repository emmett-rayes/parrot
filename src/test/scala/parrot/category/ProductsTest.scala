package parrot
package category

import Category.Type

/** The laws of [[Products]], for binary products on a category whose objects are all types. */
abstract class ProductsSpec(
  tracked override val K: Category { type Obj = Type },
  tracked override val B: Products.Of[K.type],
)(using
  category: CategoryFixture.On[K.type],
  typename: TypeName[B.Self],
  types: SampleTypes,
  sample: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[B.F[X, Y]],
) extends BifunctorSpec(K, B, "Products") {
  import types.{T1, T2, T3, T4, given}
  import category.*
  import K.-->
  import B.F
  import B.ProductsLaws.*

  private given BSample: [X: Sample, Y: Sample] => Sample[F[X, Y]] = sample[X, Y]

  also("Products") {
    law("fstPair") {
      val observations = observe[T1, T2]
      val fs           = arrow[T1, T2]
      val gs           = arrow[T1, T3]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((T1 --> T2) is Observable) = observe
        fstPair(f, g)
      }
    }

    law("sndPair") {
      val observations = observe[T1, T3]
      val fs           = arrow[T1, T2]
      val gs           = arrow[T1, T3]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((T1 --> T3) is Observable) = observe
        sndPair(f, g)
      }
    }

    law("pairUniqueness") {
      val observations = observe[T1, F[T2, T3]]
      val hs           = arrow[T1, F[T2, T3]]

      forAll(observations, hs) { (observe, h) =>
        given ((T1 --> F[T2, T3]) is Observable) = observe
        pairUniqueness[T1, T2, T3](h)
      }
    }

    law("pairCongruence") {
      val observations = observe[T1, F[T2, T3]]
      val fs           = arrow[T1, T2]
      val gs           = arrow[T1, T3]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((T1 --> F[T2, T3]) is Observable) = observe
        pairCongruence(f, variant(f), g, variant(g))
      }
    }

    law("bimapIsPairing") {
      val observations = observe[F[T1, T2], F[T4, T3]]
      val fs           = arrow[T1, T4]
      val gs           = arrow[T2, T3]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((F[T1, T2] --> F[T4, T3]) is Observable) = observe
        bimapIsPairing(f, g)
      }
    }
  }
}

class ScalaTuple2IsProductsTest extends ProductsSpec(Total, Total.Tuple2IsProducts)
