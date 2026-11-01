package parrot
package category

import Category.Type

/** The laws of [[Symmetric]], for structures on a category whose objects are all types. */
abstract class SymmetricSpec(
  tracked override val M: Symmetric { val K: Category { type Obj = Type } },
  structure: String = "Symmetric",
)(using
  category: CategoryFixture.On[M.K.type],
  typename: TypeName[M.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[M.Tensor[X, Y]],
  unit: Sample[M.I],
) extends MonoidalSpec(M, structure) {
  import types.{T1, T2, T3, T4, given}
  import category.*
  import M.K.-->
  import M.`*`
  import M.SymmetricLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[M.Tensor[X, Y]] = tensor[X, Y]

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

    law("symmetry") {
      val observations = observe[T1 * T2, T1 * T2]

      forAll(observations) { observe =>
        given (((T1 * T2) --> (T1 * T2)) is Observable) = observe
        symmetry[T1, T2]
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

class PartialProductIsSymmetricTest extends SymmetricSpec(Partial.Product)
