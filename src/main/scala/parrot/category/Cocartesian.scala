package parrot
package category

import scala.annotation.targetName

/** A cocartesian monoidal structure on a category **C**.
  *
  * Represents a category with finite coproducts, where
  *   - *A* + *B* is the coproduct
  *   - *ι*₁ and *ι*₂ are the injections
  *   - [*f*,*g*] is the copairing of *f* and *g*
  *   - *I* is the unit
  *   - ¡ creates a given object from the unit
  *   - ∇ merges the coproduct of an object with itself into the object
  *
  * In a cocartesian category, the tensor is the categorical coproduct and the unit is an initial object. The unitors,
  * the associator and the braiding are derived from the injections and copairing.
  */
abstract class Cocartesian(
  tracked override val category: Category,
  tracked override val unit: Initial.Of[category.type],
  tracked override val tensor: Coproducts.On[category.type],
) extends Symmetric(category, unit, tensor) {
  import category.{Iso, Obj, identity, -->, <->, >>>}

  /** Infix alias for [[Tensor]]. */
  final type + = Tensor

  private given IIsObj: (I is Obj)                                = unit.evidence
  private given TensorIsObj: [A: Obj, B: Obj] => ((A + B) is Obj) = tensor.objects[A, B]

  /** The unique morphism ¡: *I* → *A* from the unit. */
  final def absurd[A: Obj]: I --> A = {
    unit.absurd[A]
  }

  /** The first injection *ι*₁: *A* → *A* + *B* of the coproduct of *A* and *B*. */
  final def inl[A: Obj, B: Obj]: A --> (A + B) = {
    tensor.coproduct[A, B].inl
  }

  /** The second injection *ι*₂: *B* → *A* + *B* of the coproduct of *A* and *B*. */
  final def inr[A: Obj, B: Obj]: B --> (A + B) = {
    tensor.coproduct[A, B].inr
  }

  /** The copairing [*f*,*g*]: *A* + *B* → *X* of *f*: *A* → *X* and *g*: *B* → *X* in the coproduct of *A* and *B*. */
  final def copair[A: Obj, B: Obj, X: Obj](f: A --> X, g: B --> X): (A + B) --> X = {
    tensor.coproduct[A, B].copair(f, g)
  }

  /** The codiagonal ∇: *A* + *A* → *A*. */
  final def codiagonal[A: Obj]: (A + A) --> A = {
    identity[A] ||| identity[A]
  }

  /** Every object is a monoid in exactly one way: creating with ¡ and merging with ∇. */
  final def monoid[X: Obj]: Monoid.In[this.type] { type Self = X } = {
    new Monoid(this) {
      type Self = X

      def evidence: X is Obj = summon

      def unit: I --> X = absurd[X]

      def multiply: (X + X) --> X = codiagonal[X]
    }
  }

  /** The corresponding cartesian opposite **C**ᵒᵖ. */
  override lazy val op: Cocartesian.Op.Of[this.type] = Cocartesian.Op(this)

  extension [A: Obj, X: Obj](f: A --> X)
    /** Infix extension for [[copair]]. */
    @targetName("copairExt")
    final def |||[B: Obj](g: B --> X): (A + B) --> X = {
      copair(f, g)
    }

  extension [A: Obj, B: Obj](f: A --> B)
    /** Infix extension for [[parallel]] on coproducts. */
    final def +++[C: Obj, D: Obj](g: C --> D): (A + C) --> (B + D) = {
      parallel(f, g)
    }

  /** *σ* = [*ι*₂,*ι*₁]
    */
  def braid[A: Obj, B: Obj]: (A + B) --> (B + A) = {
    inr[B, A] ||| inl[B, A]
  }

  /** *λ* = [¡,*id*] and *λ*⁻¹ = *ι*₂
    */
  def leftUnitor[A: Obj]: (I + A) <-> A = {
    Iso(absurd[A] ||| identity[A], inr[I, A])
  }

  /** *ρ* = [*id*,¡] and *ρ*⁻¹ = *ι*₁
    */
  override def rightUnitor[A: Obj]: (A + I) <-> A = {
    Iso(identity[A] ||| absurd[A], inl[A, I])
  }

  /** *α* = [[*ι*₁,*ι*₂ ∘ *ι*₁],*ι*₂ ∘ *ι*₂] and *α*⁻¹ = [*ι*₁ ∘ *ι*₁,[*ι*₁ ∘ *ι*₂,*ι*₂]]
    */
  def associator[A: Obj, B: Obj, C: Obj]: ((A + B) + C) <-> (A + (B + C)) = {
    Iso(
      (inl[A, B + C] ||| (inl[B, C] >>> inr[A, B + C])) ||| (inr[B, C] >>> inr[A, B + C]),
      (inl[A, B] >>> inl[A + B, C]) ||| ((inr[A, B] >>> inl[A + B, C]) ||| inr[A + B, C]),
    )
  }

  /** Laws that any `Cocartesian` structure must satisfy. */
  object CocartesianLaws {

    /** *σ* = [*ι*₂,*ι*₁]
      */
    def braidIsCopairing[A: Obj, B: Obj](using ((A + B) --> (B + A)) is Observable): Boolean = {
      braid[A, B] =?= (inr[B, A] ||| inl[B, A])
    }

    /** *λ*⁻¹ = *ι*₂
      */
    def leftUnitorInverseIsInr[A: Obj](using (A --> (I + A)) is Observable): Boolean = {
      leftUnitor[A].from =?= inr[I, A]
    }

    /** *ρ*⁻¹ = *ι*₁
      */
    def rightUnitorInverseIsInl[A: Obj](using (A --> (A + I)) is Observable): Boolean = {
      rightUnitor[A].from =?= inl[A, I]
    }

    /** *α* = [[*ι*₁,*ι*₂ ∘ *ι*₁],*ι*₂ ∘ *ι*₂]
      */
    def associatorIsCopairing[A: Obj, B: Obj, C: Obj](
      using (((A + B) + C) --> (A + (B + C))) is Observable
    ): Boolean = {
      val copairing = (inl[A, B + C] ||| (inl[B, C] >>> inr[A, B + C])) ||| (inr[B, C] >>> inr[A, B + C])
      associator[A, B, C].to =?= copairing
    }
  }
}

object Cocartesian {

  /** The cocartesian monoidal structures on a category **C**. */
  type On[C <: Category] = Cocartesian { val category: C }

  /** The cartesian opposite **C**ᵒᵖ of a cocartesian category **C**.
    *
    * The coproducts, injections and copairing in **C** become products, projections and pairing in **C**ᵒᵖ.
    */
  final class Op(tracked val cocartesian: Cocartesian)
      extends Cartesian(cocartesian.category.op, cocartesian.unit.op, cocartesian.tensor.op)

  object Op {

    /** The cartesian opposite of a cocartesian category **C**. */
    type Of[C <: Cocartesian] = Op { val cocartesian: C }
  }
}
