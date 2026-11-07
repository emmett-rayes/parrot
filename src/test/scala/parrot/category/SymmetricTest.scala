package parrot
package category

import Category.Type

/** The laws of [[Symmetric]], those of [[SymmetricPremonoidal]] and [[Monoidal]], for structures on a category whose
  * objects are all types.
  */
abstract class SymmetricSpec(
  tracked override val premonoidal: Symmetric.On[Category { type Obj = Type }],
  structure: String = "Symmetric",
)(using
  category: CategoryFixture.For[premonoidal.category.type],
  typename: TypeName[premonoidal.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[premonoidal.Tensor[X, Y]],
  unit: Sample[premonoidal.I],
) extends SymmetricPremonoidalSpec(s"${typename.name} on ${category.name}", premonoidal, structure) {
  import types.{T1, T2, T3, T4, given}
  import category.*
  import premonoidal.`*`
  import premonoidal.category.-->

  private given TensorSample: [X: Sample, Y: Sample] => Sample[premonoidal.Tensor[X, Y]] = tensor[X, Y]

  also("Monoidal") {
    import premonoidal.MonoidalLaws.*

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
  }
}

class PartialProductIsSymmetricTest   extends SymmetricSpec(Partial.Product)
class PartialProductOpIsSymmetricTest extends SymmetricSpec(Partial.Product.op)
