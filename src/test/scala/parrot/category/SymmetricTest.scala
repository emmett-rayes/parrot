package parrot
package category

import Category.Type

/** The laws of [[Symmetric]], for structures on a category whose objects are all types. */
abstract class SymmetricSpec(
  tracked override val premonoidal: Symmetric.On[Category { type Obj = Type }],
  structure: String = "Symmetric",
)(using
  category: CategoryFixture.For[premonoidal.category.type],
  typename: TypeName[premonoidal.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[premonoidal.Tensor[X, Y]],
  unit: Sample[premonoidal.I],
) extends MonoidalSpec(premonoidal, structure) {
  import types.{T1, T2, T3, T4, given}
  import category.*
  import premonoidal.category.-->
  import premonoidal.`*`
  import premonoidal.SymmetricLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[premonoidal.Tensor[X, Y]] = tensor[X, Y]

  also("Symmetric") {
    law("braidNaturality") {
      val observations = observe[T1 * T2, T3 * T4]
      val fs           = arrow[T1, T4]
      val gs           = arrow[T2, T3]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given (((T1 * T2) --> (T3 * T4)) is Observable) = observe
        braidNaturality(f, g)
      }
    }

    law("involution") {
      val observations = observe[T1 * T2, T1 * T2]

      forAll(observations) { observe =>
        given (((T1 * T2) --> (T1 * T2)) is Observable) = observe
        involution[T1, T2]
      }
    }

    law("hexagon") {
      val observations = observe[(T1 * T2) * T4, T2 * (T4 * T1)]

      forAll(observations) { observe =>
        given ((((T1 * T2) * T4) --> (T2 * (T4 * T1))) is Observable) = observe
        hexagon[T1, T2, T4]
      }
    }
  }
}

class PartialProductIsSymmetricTest   extends SymmetricSpec(Partial.Product)
class PartialProductOpIsSymmetricTest extends SymmetricSpec(Partial.Product.op)
