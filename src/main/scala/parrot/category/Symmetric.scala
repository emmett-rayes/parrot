package parrot
package category

/** A symmetric monoidal structure on a category **C**.
  *
  * Represents a symmetric monoidal category, where
  *   - *σ*: *A* ⊗ *B* ≅ *B* ⊗ *A* is the braiding
  */
abstract class Symmetric(
  tracked override val category: Category,
  tracked override val unit: category.Object,
  tracked override val tensor: Endobifunctor.On[category.type],
) extends Monoidal(category, unit, tensor) {
  import category.{Iso, Obj, -->, <->, >>>}

  /** The braiding *σ*: *A* ⊗ *B* → *B* ⊗ *A*.
    *
    * @note The braiding is its own inverse. See [[braiding]].
    */
  def braid[A: Obj, B: Obj]: (A * B) --> (B * A)

  private given IIsObj: (I is Obj)                                = unit.evidence
  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = tensor.objects[A, B]

  /** The braiding isomorphism *σ*: *A* ⊗ *B* ≅ *B* ⊗ *A*. */
  final def braiding[A: Obj, B: Obj]: (A * B) <-> (B * A) = {
    Iso(braid[A, B], braid[B, A])
  }

  /** *ρ* = *λ* ∘ *σ* and *ρ*⁻¹ = *σ* ∘ *λ*⁻¹
    */
  def rightUnitor[A: Obj]: (A * I) <-> A = {
    Iso(braid[A, I] >>> leftUnitor[A].to, leftUnitor[A].from >>> braid[I, A])
  }

  /** The corresponding opposite **C**ᵒᵖ, with the same tensor and unit.
    *
    * @note [[Cartesian]] and [[Cocartesian]] refine it to the cocartesian and the cartesian opposite.
    */
  lazy val op: Symmetric.On[category.op.type] {
    val unit: Category.Object { type Self = Symmetric.this.I }
    val tensor: Bifunctor { type Self = Symmetric.this.tensor.F }
  } = Symmetric.Op(this)

  /** Laws that any `Symmetric` structure must satisfy. */
  object SymmetricLaws {

    /** (*g* ⊗ *f*) ∘ *σ* = *σ* ∘ (*f* ⊗ *g*) */
    def braidNaturality[A: Obj, B: Obj, C: Obj, D: Obj](f: A --> B, g: C --> D)(
      using ((A * C) --> (D * B)) is Observable
    ): Boolean = {
      (braid[A, C] >>> (g *** f)) =?= ((f *** g) >>> braid[B, D])
    }

    /** *σ* ∘ *σ* = *id*
      */
    def involution[A: Obj, B: Obj](using ((A * B) --> (A * B)) is Observable): Boolean = {
      (braid[A, B] >>> braid[B, A]) =?= category.identity[A * B]
    }

    /** *α* ∘ *σ* ∘ *α* = (*id* ⊗ *σ*) ∘ *α* ∘ (*σ* ⊗ *id*)
      */
    def hexagon[A: Obj, B: Obj, C: Obj](using (((A * B) * C) --> (B * (C * A))) is Observable): Boolean = {
      val lhs = associator[A, B, C].to >>> braid[A, B * C] >>> associator[B, C, A].to
      val rhs = (braid[A, B] *** category.identity[C]) >>> associator[B, A, C].to >>>
        (category.identity[B] *** braid[A, C])
      lhs =?= rhs
    }
  }
}

object Symmetric {

  /** The symmetric monoidal structures on a category **C**. */
  type On[C <: Category] = Symmetric { val category: C }

  /** The opposite **C**ᵒᵖ of a symmetric monoidal category **C**.
    *
    * The opposite symmetric monoidal category has the same tensor and unit, with the unitors, the associator and the
    * braiding reversed.
    */
  final class Op(tracked val symmetric: Symmetric)
      extends Symmetric(
        symmetric.category.op,
        symmetric.category.op.Object[symmetric.I](using symmetric.unit.evidence),
        symmetric.tensor.op,
      ) {
    import category.{Iso, Obj, -->, <->}

    private given IIsObj: (I is Obj)                                = unit.evidence
    private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = tensor.objects[A, B]

    def leftUnitor[A: Obj]: (I * A) <-> A = {
      Iso(symmetric.leftUnitor[A].from, symmetric.leftUnitor[A].to)
    }

    def associator[A: Obj, B: Obj, C: Obj]: ((A * B) * C) <-> (A * (B * C)) = {
      Iso(symmetric.associator[A, B, C].from, symmetric.associator[A, B, C].to)
    }

    def braid[A: Obj, B: Obj]: (A * B) --> (B * A) = {
      symmetric.braid[B, A]
    }
  }

  object Op {

    /** The opposite of a symmetric monoidal category **C**. */
    type Of[C <: Symmetric] = Op { val symmetric: C }
  }
}
