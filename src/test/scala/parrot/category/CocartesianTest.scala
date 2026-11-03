package parrot
package category

import Category.Type

/** The laws of [[Cocartesian]]: the unitors, the associator and the braiding are those of the coproducts. */
abstract class CocartesianSpec(
  tracked override val monoidal: Cocartesian { val category: Category { type Obj = Type } },
)(using
  category: CategoryFixture.For[monoidal.category.type],
  typename: TypeName[monoidal.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[monoidal.Tensor[X, Y]],
  unit: Sample[monoidal.I],
) extends SymmetricSpec(monoidal, "Cocartesian") {
  import types.{T1, T2, T3, given}
  import category.*
  import monoidal.category.-->
  import monoidal.{I, +}
  import monoidal.CocartesianLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[monoidal.Tensor[X, Y]] = tensor[X, Y]

  law("braidIsCopairing") {
    val observations = observe[T1 + T2, T2 + T1]

    forAll(observations) { observe =>
      given (((T1 + T2) --> (T2 + T1)) is Observable) = observe
      braidIsCopairing[T1, T2]
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
