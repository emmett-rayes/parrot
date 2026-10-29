package parrot
package category

/** The laws of [[Monoidal]], for structures on a category whose objects are all types. */
abstract class MonoidalSpec(tracked val M: Monoidal { val K: Category { type Obj = Type } })(using
  category: CategoryFixture.On[M.K.type],
  typename: TypeName[M.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[M.Tensor[X, Y]],
  unit: Sample[M.I],
) extends LawSuite("Monoidal", s"${typename.name} on ${category.name}") {
  import types.{T1, T2, T3, T4, given}
  import category.*
  import M.{I, `*`}
  import M.K.-->
  import M.MonoidalLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[M.Tensor[X, Y]] = tensor[X, Y]

  law("leftUnitorIsomorphism") {
    val observations1 = observe[I * T1, I * T1]
    val observations2 = observe[T1, T1]

    forAll(observations1, observations2) { (o1, o2) =>
      given O1: (((I * T1) --> (I * T1)) is Observable) = o1
      given O2: ((T1 --> T1) is Observable)             = o2
      leftUnitorIsomorphism[T1]
    }
  }

  law("rightUnitorIsomorphism") {
    val observations1 = observe[T1 * I, T1 * I]
    val observations2 = observe[T1, T1]

    forAll(observations1, observations2) { (o1, o2) =>
      given O1: (((T1 * I) --> (T1 * I)) is Observable) = o1
      given O2: ((T1 --> T1) is Observable)             = o2
      rightUnitorIsomorphism[T1]
    }
  }

  law("associatorIsomorphism") {
    val observations1 = observe[(T1 * T2) * T4, (T1 * T2) * T4]
    val observations2 = observe[T1 * (T2 * T4), T1 * (T2 * T4)]

    forAll(observations1, observations2) { (o1, o2) =>
      given O1: ((((T1 * T2) * T4) --> ((T1 * T2) * T4)) is Observable) = o1
      given O2: (((T1 * (T2 * T4)) --> (T1 * (T2 * T4))) is Observable) = o2
      associatorIsomorphism[T1, T2, T4]
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

class TotalProductIsMonoidalTest     extends MonoidalSpec(Total.Product)
class ScalaCoproductIsMonoidalTest   extends MonoidalSpec(Total.Coproduct)
class PartialProductIsMonoidalTest   extends MonoidalSpec(Partial.Product)
class PartialCoproductIsMonoidalTest extends MonoidalSpec(Partial.Coproduct)
