package parrot
package category

/** A monoidal structure on a category **C**.
  *
  * Represents a monoidal category (**C**, ⊗, *I*), a premonoidal category where
  *   - ⊗: **C** × **C** → **C** is the tensor, a bifunctor with the whiskerings *f* ⦸ *C* = *f* ⊗ *id* and
  *     *C* ⊘ *f* = *id* ⊗ *f*
  *   - every morphism is central, and *f* ⊗ *g* is the tensor of morphisms
  */
abstract class Monoidal(
  tracked override val category: Category,
  tracked override val unit: category.Object,
  tracked override val tensor: Endobifunctor.On[category.type],
) extends Premonoidal(category, unit, tensor) {
  import category.{Obj, -->, >>>}

  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = tensor.objects[A, B]

  /** The tensor of morphisms *f* ⊗ *g*. */
  final def parallel[A: Obj, B: Obj, C: Obj, D: Obj](f: A --> B, g: C --> D): (A * C) --> (B * D) = {
    tensor.bimap(f, g)
  }

  extension [A: Obj, B: Obj](f: A --> B)
    /** Infix extension for [[parallel]]. */
    final def ***[C: Obj, D: Obj](g: C --> D): (A * C) --> (B * D) = {
      parallel(f, g)
    }

  /** Laws that any `Monoidal` structure must satisfy.
    *
    * Beyond the laws of a premonoidal category, the associator is natural in all its components at once.
    */
  object MonoidalLaws {

    /** (*f* ⊗ (*g* ⊗ *h*)) ∘ *α* = *α* ∘ ((*f* ⊗ *g*) ⊗ *h*) */
    def associatorNaturality[A: Obj, B: Obj, C: Obj, D: Obj, E: Obj, F: Obj](
      f: A --> B,
      g: C --> D,
      h: E --> F,
    )(using (((A * C) * E) --> (B * (D * F))) is Observable): Boolean = {
      (associator[A, C, E].to >>> (f *** (g *** h))) =?= (((f *** g) *** h) >>> associator[B, D, F].to)
    }
  }
}

object Monoidal {

  /** The monoidal structures on a category **C**. */
  type On[C <: Category] = Monoidal { val category: C }
}
