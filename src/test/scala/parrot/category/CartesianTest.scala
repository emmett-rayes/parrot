package parrot
package category

import Category.Type

/** The laws of [[Cartesian]]: the unitors, the associator and the braiding are those of the products. */
abstract class CartesianSpec(
  tracked override val monoidal: Cartesian { val category: Category { type Obj = Type } },
)(using
  category: CategoryFixture.For[monoidal.category.type],
  typename: TypeName[monoidal.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[monoidal.Tensor[X, Y]],
  unit: Sample[monoidal.I],
) extends SymmetricSpec(monoidal, "Cartesian") {
  import types.{T1, T2, T3, given}
  import category.*
  import monoidal.category.-->
  import monoidal.{I, `*`}
  import monoidal.CartesianLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[monoidal.Tensor[X, Y]] = tensor[X, Y]

  law("braidIsPairing") {
    val observations = observe[T1 * T2, T2 * T1]

    forAll(observations) { observe =>
      given (((T1 * T2) --> (T2 * T1)) is Observable) = observe
      braidIsPairing[T1, T2]
    }
  }

  law("leftUnitorIsSnd") {
    val observations = observe[I * T1, T1]

    forAll(observations) { observe =>
      given (((I * T1) --> T1) is Observable) = observe
      leftUnitorIsSnd[T1]
    }
  }

  law("rightUnitorIsFst") {
    val observations = observe[T1 * I, T1]

    forAll(observations) { observe =>
      given (((T1 * I) --> T1) is Observable) = observe
      rightUnitorIsFst[T1]
    }
  }

  law("associatorIsPairing") {
    val observations = observe[(T1 * T2) * T3, T1 * (T2 * T3)]

    forAll(observations) { observe =>
      given ((((T1 * T2) * T3) --> (T1 * (T2 * T3))) is Observable) = observe
      associatorIsPairing[T1, T2, T3]
    }
  }
}

class TotalProductIsCartesianTest extends CartesianSpec(Total.Products)
class TotalLimitIsCartesianTest   extends CartesianSpec(LimitCartesian)
