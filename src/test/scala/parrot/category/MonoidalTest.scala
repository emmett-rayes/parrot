package parrot
package category

/** The laws of [[Monoidal]], for structures on a category whose objects are all types. */
abstract class MonoidalSpec(
  tracked val M: Monoidal { val K: Category { type Obj = Type } },
  structure: String = "Monoidal",
)(using
  category: CategoryFixture.On[M.K.type],
  typename: TypeName[M.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[M.Tensor[X, Y]],
  unit: Sample[M.I],
) extends LawSuite(structure, s"${typename.name} on ${category.name}") {
  import types.{T1, T2, T3, T4, given}
  import category.*
  import M.{I, `*`}
  import M.K.-->
  import M.MonoidalLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[M.Tensor[X, Y]] = tensor[X, Y]

  also("Monoidal") {
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

    law("associatorNaturality") {
      val observations = observe[(T1 * T2) * T3, T4 * (T1 * T2)]
      val fs           = arrow[T1, T4]
      val gs           = arrow[T2, T1]
      val hs           = arrow[T3, T2]

      forAll(observations, fs, gs, hs) { (observe, f, g, h) =>
        given ((((T1 * T2) * T3) --> (T4 * (T1 * T2))) is Observable) = observe
        associatorNaturality(f, g, h)
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
