package parrot
package category

/** A symmetric monoidal structure on a category **K**: a monoidal structure whose tensor can swap its arguments.
  *
  * Represents a symmetric monoidal category, where
  *   - *β*: *A* ⊗ *B* → *B* ⊗ *A* is the braiding, its own inverse
  */
abstract class Symmetric(
  tracked override val K: Category,
  tracked override val U: K.Obj,
  tracked override val T: Bifunctor { val C1: K.type; val C2: K.type; val D: K.type },
) extends Monoidal(K, U, T) {
  import K.{Obj, -->, >>>}

  /** The braiding *β*: *A* ⊗ *B* → *B* ⊗ *A*. */
  def braid[A: Obj, B: Obj]: (A * B) --> (B * A)

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
      (braid[A, B] >>> braid[B, A]) =?= K.identity[A * B]
    }

    /** *α* ∘ *β* ∘ *α* = (*id* ⊗ *β*) ∘ *α* ∘ (*β* ⊗ *id*)
      */
    def hexagon[A: Obj, B: Obj, C: Obj](using (((A * B) * C) --> (B * (C * A))) is Observable): Boolean = {
      val lhs = associator[A, B, C].to >>> braid[A, B * C] >>> associator[B, C, A].to
      val rhs = (braid[A, B] *** K.identity[C]) >>> associator[B, A, C].to >>> (K.identity[B] *** braid[A, C])
      lhs =?= rhs
    }
  }
}
