package parrot
package category

/** A symmetric monoidal structure on a category **C**.
  *
  * Represents a symmetric monoidal category, a [[Monoidal]] category with a [[SymmetricPremonoidal]] braiding *σ*.
  *
  * It has no laws of its own: naturality of *σ* in each component and the interchange law of the tensor make *σ*
  * natural in both components at once.
  */
abstract class Symmetric(
  tracked override val category: Category,
  tracked override val unit: category.Object,
  tracked override val tensor: Endobifunctor.On[category.type],
) extends Monoidal(category, unit, tensor), SymmetricPremonoidal {

  /** The corresponding opposite **C**ᵒᵖ, with the same tensor and unit.
    *
    * @note [[Cartesian]] and [[Cocartesian]] refine it to the cocartesian and the cartesian opposite.
    */
  lazy val op: Symmetric.On[category.op.type] {
    val unit: Category.Object { type Self = Symmetric.this.I }
    val tensor: Bifunctor { type Self = Symmetric.this.tensor.F }
  } = Symmetric.Op(this)
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
