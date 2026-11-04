package parrot
package category

import Category.Type

/** The laws of [[Premonoidal]], for structures on a category whose objects are all types. */
abstract class PremonoidalSpec(
  name: String,
  tracked val premonoidal: Premonoidal.On[Category { type Obj = Type }],
  structure: String = "Premonoidal",
)(using
  category: CategoryFixture.For[premonoidal.category.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[premonoidal.Tensor[X, Y]],
  unit: Sample[premonoidal.I],
) extends LawSuite(structure, name) {
  import types.{T1, T2, T3, T4, given}
  import category.*
  import premonoidal.{I, `*`}
  import premonoidal.category.-->
  import premonoidal.PremonoidalLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[premonoidal.Tensor[X, Y]] = tensor[X, Y]

  also("Premonoidal") {
    law("leftUnitorLeftInverse") {
      val observations = observe[I * T1, I * T1]

      forAll(observations) { observe =>
        given (((I * T1) --> (I * T1)) is Observable) = observe
        leftUnitorLeftInverse[T1]
      }
    }

    law("leftUnitorRightInverse") {
      val observations = observe[T1, T1]

      forAll(observations) { observe =>
        given ((T1 --> T1) is Observable) = observe
        leftUnitorRightInverse[T1]
      }
    }

    law("rightUnitorLeftInverse") {
      val observations = observe[T1 * I, T1 * I]

      forAll(observations) { observe =>
        given (((T1 * I) --> (T1 * I)) is Observable) = observe
        rightUnitorLeftInverse[T1]
      }
    }

    law("rightUnitorRightInverse") {
      val observations = observe[T1, T1]

      forAll(observations) { observe =>
        given ((T1 --> T1) is Observable) = observe
        rightUnitorRightInverse[T1]
      }
    }

    law("associatorLeftInverse") {
      val observations = observe[(T1 * T2) * T4, (T1 * T2) * T4]

      forAll(observations) { observe =>
        given ((((T1 * T2) * T4) --> ((T1 * T2) * T4)) is Observable) = observe
        associatorLeftInverse[T1, T2, T4]
      }
    }

    law("associatorRightInverse") {
      val observations = observe[T1 * (T2 * T4), T1 * (T2 * T4)]

      forAll(observations) { observe =>
        given (((T1 * (T2 * T4)) --> (T1 * (T2 * T4))) is Observable) = observe
        associatorRightInverse[T1, T2, T4]
      }
    }

    law("leftUnitorNaturality") {
      val observations = observe[I * T1, T2]
      val fs           = arrow[T1, T2]

      forAll(observations, fs) { (observe, f) =>
        given (((I * T1) --> T2) is Observable) = observe
        leftUnitorNaturality(f)
      }
    }

    law("rightUnitorNaturality") {
      val observations = observe[T1 * I, T2]
      val fs           = arrow[T1, T2]

      forAll(observations, fs) { (observe, f) =>
        given (((T1 * I) --> T2) is Observable) = observe
        rightUnitorNaturality(f)
      }
    }

    law("associatorLeftNaturality") {
      val observations = observe[(T1 * T3) * T4, T2 * (T3 * T4)]
      val fs           = arrow[T1, T2]

      forAll(observations, fs) { (observe, f) =>
        given ((((T1 * T3) * T4) --> (T2 * (T3 * T4))) is Observable) = observe
        associatorLeftNaturality[T1, T2, T3, T4](f)
      }
    }

    law("associatorMiddleNaturality") {
      val observations = observe[(T3 * T1) * T4, T3 * (T2 * T4)]
      val fs           = arrow[T1, T2]

      forAll(observations, fs) { (observe, f) =>
        given ((((T3 * T1) * T4) --> (T3 * (T2 * T4))) is Observable) = observe
        associatorMiddleNaturality[T1, T2, T3, T4](f)
      }
    }

    law("associatorRightNaturality") {
      val observations = observe[(T3 * T4) * T1, T3 * (T4 * T2)]
      val fs           = arrow[T1, T2]

      forAll(observations, fs) { (observe, f) =>
        given ((((T3 * T4) * T1) --> (T3 * (T4 * T2))) is Observable) = observe
        associatorRightNaturality[T1, T2, T3, T4](f)
      }
    }

    law("leftUnitorCentrality") {
      val observations1 = observe[(I * T1) * T2, T1 * T3]
      val observations2 = observe[T2 * (I * T1), T3 * T1]
      val gs            = arrow[T2, T3]

      forAll(observations1, observations2, gs) { (observe1, observe2, g) =>
        given O1: ((((I * T1) * T2) --> (T1 * T3)) is Observable) = observe1
        given O2: (((T2 * (I * T1)) --> (T3 * T1)) is Observable) = observe2
        leftUnitorCentrality[T1, T2, T3](g)
      }
    }

    law("rightUnitorCentrality") {
      val observations1 = observe[(T1 * I) * T2, T1 * T3]
      val observations2 = observe[T2 * (T1 * I), T3 * T1]
      val gs            = arrow[T2, T3]

      forAll(observations1, observations2, gs) { (observe1, observe2, g) =>
        given O1: ((((T1 * I) * T2) --> (T1 * T3)) is Observable) = observe1
        given O2: (((T2 * (T1 * I)) --> (T3 * T1)) is Observable) = observe2
        rightUnitorCentrality[T1, T2, T3](g)
      }
    }

    law("associatorCentrality") {
      val observations1 = observe[((T1 * T2) * T3) * T4, (T1 * (T2 * T3)) * T1]
      val observations2 = observe[T4 * ((T1 * T2) * T3), T1 * (T1 * (T2 * T3))]
      val gs            = arrow[T4, T1]

      forAll(observations1, observations2, gs) { (observe1, observe2, g) =>
        given O1: (((((T1 * T2) * T3) * T4) --> ((T1 * (T2 * T3)) * T1)) is Observable) = observe1
        given O2: (((T4 * ((T1 * T2) * T3)) --> (T1 * (T1 * (T2 * T3)))) is Observable) = observe2
        associatorCentrality[T1, T2, T3, T4, T1](g)
      }
    }

    law("triangle") {
      val observations = observe[(T1 * I) * T2, T1 * T2]

      forAll(observations) { observe =>
        given ((((T1 * I) * T2) --> (T1 * T2)) is Observable) = observe
        triangle[T1, T2]
      }
    }

    law("pentagon") {
      val observations = observe[((T1 * T2) * T3) * T4, T1 * (T2 * (T3 * T4))]

      forAll(observations) { observe =>
        given (((((T1 * T2) * T3) * T4) --> (T1 * (T2 * (T3 * T4)))) is Observable) =
          observe
        pentagon[T1, T2, T3, T4]
      }
    }
  }
}
