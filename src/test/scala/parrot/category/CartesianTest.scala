package parrot
package category

/** The laws of [[Cartesian]]: the universal property of products. */
abstract class CartesianSpec(tracked val M: Cartesian { val K: Category { type Obj = Type } })(using
  category: CategoryFixture.On[M.K.type],
  monoidal: TypeName[M.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[M.Tensor[X, Y]],
  unit: Sample[M.I],
) extends LawSuite("Cartesian", s"${monoidal.name} on ${category.name}") {
  import types.{T1, T2, T3, T4, given}
  import category.*
  import M.K.-->
  import M.CartesianLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[M.Tensor[X, Y]] = tensor[X, Y]

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
    val observations = observe[T1, M.Tensor[T2, T3]]
    val hs           = arrow[T1, M.Tensor[T2, T3]]

    forAll(observations, hs) { (observe, h) =>
      given ((T1 --> M.Tensor[T2, T3]) is Observable) = observe
      pairUniqueness(h)
    }
  }

  law("discardUniqueness") {
    val observations = observe[T1, M.I]
    val fs           = arrow[T1, M.I]

    forAll(observations, fs) { (observe, f) =>
      given ((T1 --> M.I) is Observable) = observe
      discardUniqueness(f)
    }
  }

  law("tensorIsProduct") {
    val observations = observe[M.Tensor[T1, T2], M.Tensor[T4, T3]]
    val fs           = arrow[T1, T4]
    val gs           = arrow[T2, T3]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given ((M.Tensor[T1, T2] --> M.Tensor[T4, T3]) is Observable) = observe
      tensorIsProduct(f, g)
    }
  }

  law("pairCongruence") {
    val observations = observe[T1, M.Tensor[T2, T3]]
    val fs           = arrow[T1, T2]
    val gs           = arrow[T1, T3]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given ((T1 --> M.Tensor[T2, T3]) is Observable) = observe
      pairCongruence(f, variant(f), g, variant(g))
    }
  }
}

class TotalProductIsCartesianTest extends CartesianSpec(Total.Product)
