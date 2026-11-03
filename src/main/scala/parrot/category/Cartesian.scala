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
  final lazy val op: Cartesian.Op.Of[this.type] = Cartesian.Op(this)

  extension [X: Obj, A: Obj](f: X --> A)
    /** Infix extension for [[pair]]. */
    @targetName("pairExt")
    final def &&&[B: Obj](g: X --> B): X --> (A * B) = {
      pair(f, g)
    }

  /** *β* = ⟨*π*₂,*π*₁⟩
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

  /** *α* = ⟨*π*₁ ∘ *π*₁,⟨*π*₂ ∘ *π*₁,*π*₂⟩⟩ and *α*⁻¹ = ⟨⟨*π*₁,*π*₁ ∘ *π*₂⟩, *π*₂ ∘ *π*₂⟩
    */
  def associator[A: Obj, B: Obj, C: Obj]: ((A * B) * C) <-> (A * (B * C)) = {
    Iso(
      (fst[A * B, C] >>> fst[A, B]) &&& ((fst[A * B, C] >>> snd[A, B]) &&& snd[A * B, C]),
      (fst[A, B * C] &&& (snd[A, B * C] >>> fst[B, C])) &&& (snd[A, B * C] >>> snd[B, C]),
    )
  }

  /** Laws that any `Cartesian` structure must satisfy. */
  object CartesianLaws {

    /** *β* = ⟨*π*₂,*π*₁⟩
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
  type On[K <: Category] = Cartesian { val category: K }

  /** The cocartesian opposite **C**ᵒᵖ of a cartesian category **C**.
    *
    * The products, projections and pairing in **C** become coproducts, injections and copairing in **C**ᵒᵖ.
    */
  final class Op(tracked val cartesian: Cartesian)
      extends Cocartesian(cartesian.category.op, OpInitial(cartesian), OpCoproducts(cartesian))

  object Op {

    /** The cocartesian opposite of a cartesian category **C**. */
    type Of[K <: Cartesian] = Op { val cartesian: K }
  }

  /** The terminal object of a cartesian category **C**, as the initial object of **C**ᵒᵖ: ¡ is !. */
  final class OpInitial(tracked val cartesian: Cartesian)
      extends Initial(cartesian.category.op) {
    import category.{Obj, -->}

    type Self = cartesian.I

    def evidence: Self is Obj = {
      cartesian.unit.evidence
    }

    def absurd[A: Obj]: I --> A = {
      cartesian.discard[A]
    }
  }

  /** The products of a cartesian category **C**, as the binary coproducts of **C**ᵒᵖ.
    *
    * The coproduct of two objects is their product, and the coproduct of morphisms is the product of their opposites.
    */
  final class OpCoproducts(tracked val cartesian: Cartesian) extends Coproducts(cartesian.category.op) {
    import category.{Obj, Object, -->}

    type Self = cartesian.Tensor

    def objects[A: Obj, B: Obj]: F[A, B] is Obj = {
      cartesian.tensor.objects[A, B]
    }

    def coproduct[X: Obj, Y: Obj]
      : OpCoproduct.In[cartesian.type] { val left: X is Object; val right: Y is Object } = {
      OpCoproduct(cartesian, category.Object[X], category.Object[Y])
    }

    override def bimap[A1: Obj, A2: Obj, B1: Obj, B2: Obj](f: A1 --> B1, g: A2 --> B2): F[A1, A2] --> F[B1, B2] = {
      cartesian.parallel(f, g)
    }
  }

  /** The product *A*₁ × *A*₂ in a cartesian category **C**, as a coproduct of **C**ᵒᵖ.
    *
    * The injections are the projections, and the copairing is the pairing.
    */
  final class OpCoproduct(
    tracked val cartesian: Cartesian,
    tracked override val left: cartesian.category.op.Object,
    tracked override val right: cartesian.category.op.Object,
  ) extends Coproduct(cartesian.category.op, left, right) {
    import category.{Obj, -->}

    type Self = cartesian.Tensor[A1, A2]

    private given A1IsObj: (A1 is Obj) = left.evidence

    private given A2IsObj: (A2 is Obj) = right.evidence

    def evidence: Self is Obj = {
      cartesian.tensor.objects[A1, A2]
    }

    def inl: A1 --> S = {
      cartesian.fst[A1, A2]
    }

    def inr: A2 --> S = {
      cartesian.snd[A1, A2]
    }

    def copair[X: Obj](f: A1 --> X, g: A2 --> X): S --> X = {
      cartesian.pair(f, g)
    }
  }

  object OpCoproduct {

    /** The products in a cartesian category **C**, as coproducts of **C**ᵒᵖ. */
    type In[C <: Cartesian] = OpCoproduct { val cartesian: C }
  }
}
