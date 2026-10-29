package parrot
package category

/** The laws of [[Cocartesian]]: the universal property of coproducts. */
abstract class CocartesianSpec(tracked val M: Cocartesian { val K: Category { type Obj = Type } })(using
  category: CategoryFixture.On[M.K.type],
  typename: TypeName[M.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[M.Tensor[X, Y]],
  unit: Sample[M.I],
) extends LawSuite("Cocartesian", s"${typename.name} on ${category.name}") {
  import types.{T1, T2, T3, T4, given}
  import category.*
  import M.K.-->
  import M.+
  import M.CocartesianLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[M.Tensor[X, Y]] = tensor[X, Y]

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
    val observations = observe[T1 + T2, T4]
    val hs           = arrow[T1 + T2, T4]

    forAll(observations, hs) { (observe, h) =>
      given (((T1 + T2) --> T4) is Observable) = observe
      copairUniqueness(h)
    }
  }

  law("absurdUniqueness") {
    val observations = observe[M.I, T1]
    val fs           = arrow[M.I, T1]

    forAll(observations, fs) { (observe, f) =>
      given ((M.I --> T1) is Observable) = observe
      absurdUniqueness(f)
    }
  }

  law("tensorIsCoproduct") {
    val observations = observe[T1 + T2, T4 + T3]
    val fs           = arrow[T1, T4]
    val gs           = arrow[T2, T3]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given (((T1 + T2) --> (T4 + T3)) is Observable) = observe
      tensorIsCoproduct(f, g)
    }
  }

  law("copairCongruence") {
    val observations = observe[T1 + T2, T4]
    val fs           = arrow[T1, T4]
    val gs           = arrow[T2, T4]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given (((T1 + T2) --> T4) is Observable) = observe
      copairCongruence(f, variant(f), g, variant(g))
    }
  }
}

class ScalaCoproductIsCocartesianTest   extends CocartesianSpec(Total.Coproduct)
class PartialCoproductIsCocartesianTest extends CocartesianSpec(Partial.Coproduct)
