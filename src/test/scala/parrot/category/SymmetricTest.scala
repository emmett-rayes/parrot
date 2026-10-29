package parrot
package category

/** The laws of [[Symmetric]], for structures on a category whose objects are all types. */
abstract class SymmetricSpec(tracked val M: Symmetric { val K: Category { type Obj = Type } })(using
  category: CategoryFixture.On[M.K.type],
  monoidal: TypeName[M.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[M.Tensor[X, Y]],
) extends LawSuite("Symmetric", s"${monoidal.name} on ${category.name}") {
  import types.{T1, T2, T3, T4, given}
  import category.*
  import M.K.-->
  import M.SymmetricLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[M.Tensor[X, Y]] = tensor[X, Y]

  private type T[X, Y] = M.Tensor[X, Y]

  law("braidNaturality") {
    val observations = observe[T[T1, T2], T[T3, T4]]
    val fs           = arrow[T1, T4]
    val gs           = arrow[T2, T3]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given ((T[T1, T2] --> T[T3, T4]) is Observable) = observe
      braidNaturality(f, g)
    }
  }

  law("symmetry") {
    val observations = observe[T[T1, T2], T[T1, T2]]

    forAll(observations) { observe =>
      given ((T[T1, T2] --> T[T1, T2]) is Observable) = observe
      symmetry[T1, T2]
    }
  }

  law("hexagon") {
    val observations = observe[T[T[T1, T2], T4], T[T2, T[T4, T1]]]

    forAll(observations) { observe =>
      given ((T[T[T1, T2], T4] --> T[T2, T[T4, T1]]) is Observable) = observe
      hexagon[T1, T2, T4]
    }
  }
}

class TotalProductIsSymmetricTest     extends SymmetricSpec(Total.Product)
class ScalaCoproductIsSymmetricTest   extends SymmetricSpec(Total.Coproduct)
class PartialProductIsSymmetricTest   extends SymmetricSpec(Partial.Product)
class PartialCoproductIsSymmetricTest extends SymmetricSpec(Partial.Coproduct)
