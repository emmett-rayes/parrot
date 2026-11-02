package parrot
package category

/** A symmetric monoidal structure on a category **K**.
  *
  * Represents a symmetric monoidal category, where
  *   - *β*: *A* ⊗ *B* ≅ *B* ⊗ *A* is the braiding
  */
abstract class Symmetric(
  tracked override val category: Category,
  tracked override val unit: category.Object,
  tracked override val tensor: Endobifunctor.On[category.type],
) extends Monoidal(category, unit, tensor) {
  import category.{Iso, Obj, -->, <->, >>>}

  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = tensor.objects[A, B]

  /** The braiding *β*: *A* ⊗ *B* → *B* ⊗ *A*.
    *
    * @note The braiding is its own inverse. See [[braiding]].
    */
  def braid[A: Obj, B: Obj]: (A * B) --> (B * A)

  /** The braiding isomorphism *β*: *A* ⊗ *B* ≅ *B* ⊗ *A*. */
  final def braiding[A: Obj, B: Obj]: (A * B) <-> (B * A) = {
    Iso(braid[A, B], braid[B, A])
  }

  /** Laws that any `Symmetric` structure must satisfy. */
  object SymmetricLaws {

    /** (*g* ⊗ *f*) ∘ *β* = *β* ∘ (*f* ⊗ *g*) */
    def braidNaturality[A: Obj, B: Obj, C: Obj, D: Obj](f: A --> B, g: C --> D)(
      using ((A * C) --> (D * B)) is Observable
    ): Boolean = {
      (braid[A, C] >>> (g *** f)) =?= ((f *** g) >>> braid[B, D])
    }

    /** *β* ∘ *β* = *id*
      */
    def symmetry[A: Obj, B: Obj](using ((A * B) --> (A * B)) is Observable): Boolean = {
      (braid[A, B] >>> braid[B, A]) =?= category.identity[A * B]
    }

    /** *α* ∘ *β* ∘ *α* = (*id* ⊗ *β*) ∘ *α* ∘ (*β* ⊗ *id*)
      */
    def hexagon[A: Obj, B: Obj, C: Obj](using (((A * B) * C) --> (B * (C * A))) is Observable): Boolean = {
      val lhs = associator[A, B, C].to >>> braid[A, B * C] >>> associator[B, C, A].to
      val rhs = (braid[A, B] *** category.identity[C]) >>> associator[B, A, C].to >>>
        (category.identity[B] *** braid[A, C])
      lhs =?= rhs
    }
  }
}
