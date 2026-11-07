package parrot
package category

import Category.Type

/** The laws of [[Cocartesian]]: the unitors, the associator and the braiding are those of the coproducts. */
abstract class CocartesianSpec(
  tracked override val premonoidal: Cocartesian.On[Category { type Obj = Type }],
)(using
  category: CategoryFixture.For[premonoidal.category.type],
  typename: TypeName[premonoidal.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[premonoidal.Tensor[X, Y]],
  unit: Sample[premonoidal.I],
) extends SymmetricSpec(premonoidal, "Cocartesian") {
  import types.{T1, T2, T3, given}
  import category.*
  import premonoidal.category.-->
  import premonoidal.{I, +}
  import premonoidal.CocartesianLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[premonoidal.Tensor[X, Y]] = tensor[X, Y]

  law("braidIsCopairing") {
    val observations = observe[T1 + T2, T2 + T1]

    forAll(observations) { observe =>
      given (((T1 + T2) --> (T2 + T1)) is Observable) = observe
      braidIsCopairing[T1, T2]
    }
  }

  law("codiagonalIsCopairing") {
    val observations = observe[T1 + T1, T1]

    forAll(observations) { observe =>
      given (((T1 + T1) --> T1) is Observable) = observe
      codiagonalIsCopairing[T1]
    }
  }

  law("leftUnitorInverseIsInr") {
    val observations = observe[T1, I + T1]

    forAll(observations) { observe =>
      given ((T1 --> (I + T1)) is Observable) = observe
      leftUnitorInverseIsInr[T1]
    }
  }

  law("rightUnitorInverseIsInl") {
    val observations = observe[T1, T1 + I]

    forAll(observations) { observe =>
      given ((T1 --> (T1 + I)) is Observable) = observe
      rightUnitorInverseIsInl[T1]
    }
  }

  law("associatorIsCopairing") {
    val observations = observe[(T1 + T2) + T3, T1 + (T2 + T3)]

    forAll(observations) { observe =>
      given ((((T1 + T2) + T3) --> (T1 + (T2 + T3))) is Observable) = observe
      associatorIsCopairing[T1, T2, T3]
    }
  }
}

class ScalaCoproductIsCocartesianTest   extends CocartesianSpec(Total.Coproducts)
class PartialCoproductIsCocartesianTest extends CocartesianSpec(Partial.Coproduct)
class TotalColimitIsCocartesianTest     extends CocartesianSpec(ColimitCocartesian)
class PartialColimitIsCocartesianTest   extends CocartesianSpec(PartialColimitCocartesian)
