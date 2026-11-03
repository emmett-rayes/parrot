package parrot
package category

import scala.annotation.targetName

/** A cartesian monoidal structure on a category **C**.
  *
  * Represents a category with finite products, where
  *   - *A* ⊗ *B* is the product
  *   - *π*₁ and *π*₂ are the projections
  *   - ⟨*f*,*g*⟩ is the pairing of *f* and *g*
  *   - *I* is the unit
  *   - ! deletes a given object to the unit
  *   - Δ copies an object to its product with itself
  *
  * In a cartesian category, the tensor is the categorical product and the unit is a terminal object. The unitors, the
  * associator and the braiding are derived from the projections and pairing.
  */
abstract class Cartesian(
  tracked override val category: Category,
  tracked override val unit: Terminal.Of[category.type],
  tracked override val tensor: Products.On[category.type],
) extends Symmetric(category, unit, tensor) {
  import category.{Iso, Obj, identity, -->, <->, >>>}

  private given IIsObj: (I is Obj)                                = unit.evidence
  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = tensor.objects[A, B]

  /** The unique morphism !: *A* → *I* to the unit. */
  final def discard[A: Obj]: A --> I = {
    unit.discard[A]
  }

  /** The first projection *π*₁: *A* ⊗ *B* → *A* of the product of *A* and *B*. */
  final def fst[A: Obj, B: Obj]: (A * B) --> A = {
    tensor.product[A, B].fst
  }

  /** The second projection *π*₂: *A* ⊗ *B* → *B* of the product of *A* and *B*. */
  final def snd[A: Obj, B: Obj]: (A * B) --> B = {
    tensor.product[A, B].snd
  }

  /** The pairing ⟨*f*,*g*⟩: *X* → *A* ⊗ *B* of *f*: *X* → *A* and *g*: *X* → *B* in the product of *A* and *B*. */
  final def pair[X: Obj, A: Obj, B: Obj](f: X --> A, g: X --> B): X --> (A * B) = {
    tensor.product[A, B].pair(f, g)
  }

  /** The diagonal Δ: *A* → *A* ⊗ *A*. */
  final def diagonal[A: Obj]: A --> (A * A) = {
    identity[A] &&& identity[A]
  }

  /** Every object is a comonoid in exactly one way: deleting with ! and copying with Δ. */
  final def comonoid[A: Obj]: Comonoid.In[this.type] { type Self = A } = {
    new Comonoid(this) {
      type Self = A

      def carrier: A is Obj = summon[A is Obj]

      def counit: A --> I = discard[A]

      def comultiply: A --> (A * A) = diagonal[A]
    }
  }

  /** The corresponding cocartesian opposite **C**ᵒᵖ. */
  override lazy val op: Cartesian.Op.Of[this.type] = Cartesian.Op(this)

  extension [X: Obj, A: Obj](f: X --> A)
    /** Infix extension for [[pair]]. */
    @targetName("pairExt")
    final def &&&[B: Obj](g: X --> B): X --> (A * B) = {
      pair(f, g)
    }

  /** *σ* = ⟨*π*₂,*π*₁⟩
    */
  def braid[A: Obj, B: Obj]: (A * B) --> (B * A) = {
    snd[A, B] &&& fst[A, B]
  }

  /** *λ* = *π*₂ and *λ*⁻¹ = ⟨!,*id*⟩
    */
  def leftUnitor[A: Obj]: (I * A) <-> A = {
    Iso(snd[I, A], discard[A] &&& identity[A])
  }

  /** *ρ* = *π*₁ and *ρ*⁻¹ = ⟨*id*,!⟩
    */
  def rightUnitor[A: Obj]: (A * I) <-> A = {
    Iso(fst[A, I], identity[A] &&& discard[A])
  }

  /** *α* = ⟨*π*₁ ∘ *π*₁,⟨*π*₂ ∘ *π*₁,*π*₂⟩⟩ and *α*⁻¹ = ⟨⟨*π*₁,*π*₁ ∘ *π*₂⟩,*π*₂ ∘ *π*₂⟩
    */
  def associator[A: Obj, B: Obj, C: Obj]: ((A * B) * C) <-> (A * (B * C)) = {
    Iso(
      (fst[A * B, C] >>> fst[A, B]) &&& ((fst[A * B, C] >>> snd[A, B]) &&& snd[A * B, C]),
      (fst[A, B * C] &&& (snd[A, B * C] >>> fst[B, C])) &&& (snd[A, B * C] >>> snd[B, C]),
    )
  }

  /** Laws that any `Cartesian` structure must satisfy. */
  object CartesianLaws {

    /** *σ* = ⟨*π*₂,*π*₁⟩
      */
    def braidIsPairing[A: Obj, B: Obj](using ((A * B) --> (B * A)) is Observable): Boolean = {
      braid[A, B] =?= (snd[A, B] &&& fst[A, B])
    }

    /** *λ* = *π*₂
      */
    def leftUnitorIsSnd[A: Obj](using ((I * A) --> A) is Observable): Boolean = {
      leftUnitor[A].to =?= snd[I, A]
    }

    /** *ρ* = *π*₁
      */
    def rightUnitorIsFst[A: Obj](using ((A * I) --> A) is Observable): Boolean = {
      rightUnitor[A].to =?= fst[A, I]
    }

    /** *α* = ⟨*π*₁ ∘ *π*₁,⟨*π*₂ ∘ *π*₁,*π*₂⟩⟩
      */
    def associatorIsPairing[A: Obj, B: Obj, C: Obj](
      using (((A * B) * C) --> (A * (B * C))) is Observable
    ): Boolean = {
      val pairing = (fst[A * B, C] >>> fst[A, B]) &&& ((fst[A * B, C] >>> snd[A, B]) &&& snd[A * B, C])
      associator[A, B, C].to =?= pairing
    }
  }
}

object Cartesian {

  /** The cartesian monoidal structures on a category **C**. */
  type On[C <: Category] = Cartesian { val category: C }

  /** The cocartesian opposite **C**ᵒᵖ of a cartesian category **C**.
    *
    * The products, projections and pairing in **C** become coproducts, injections and copairing in **C**ᵒᵖ.
    */
  final class Op(tracked val cartesian: Cartesian)
      extends Cocartesian(cartesian.category.op, cartesian.unit.op, cartesian.tensor.op)

  object Op {

    /** The cocartesian opposite of a cartesian category **C**. */
    type Of[C <: Cartesian] = Op { val cartesian: C }
  }
}
