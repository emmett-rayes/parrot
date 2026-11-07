package parrot
package category

import Category.Type

/** The laws of [[SymmetricPremonoidal]], for structures on a category whose objects are all types. */
abstract class SymmetricPremonoidalSpec(
  name: String,
  tracked override val premonoidal: SymmetricPremonoidal.On[Category { type Obj = Type }],
  structure: String = "SymmetricPremonoidal",
)(using
  category: CategoryFixture.For[premonoidal.category.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[premonoidal.Tensor[X, Y]],
  unit: Sample[premonoidal.I],
) extends PremonoidalSpec(name, premonoidal, structure) {
  import types.{T1, T2, T3, T4, given}
  import category.*
  import premonoidal.category.-->
  import premonoidal.`*`
  import premonoidal.SymmetricPremonoidalLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[premonoidal.Tensor[X, Y]] = tensor[X, Y]

  also("SymmetricPremonoidal") {
    law("braidLeftNaturality") {
      val observations = observe[T1 * T3, T3 * T2]
      val fs           = arrow[T1, T2]

      forAll(observations, fs) { (observe, f) =>
        given (((T1 * T3) --> (T3 * T2)) is Observable) = observe
        braidLeftNaturality[T1, T2, T3](f)
      }
    }

    law("braidRightNaturality") {
      val observations = observe[T3 * T1, T2 * T3]
      val fs           = arrow[T1, T2]

      forAll(observations, fs) { (observe, f) =>
        given (((T3 * T1) --> (T2 * T3)) is Observable) = observe
        braidRightNaturality[T1, T2, T3](f)
      }
    }

    law("braidCentrality") {
      val observations1 = observe[(T1 * T2) * T3, (T2 * T1) * T4]
      val observations2 = observe[T3 * (T1 * T2), T4 * (T2 * T1)]
      val gs            = arrow[T3, T4]

      forAll(observations1, observations2, gs) { (observe1, observe2, g) =>
        given O1: ((((T1 * T2) * T3) --> ((T2 * T1) * T4)) is Observable) = observe1
        given O2: (((T3 * (T1 * T2)) --> (T4 * (T2 * T1))) is Observable) = observe2
        braidCentrality[T1, T2, T3, T4](g)
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
