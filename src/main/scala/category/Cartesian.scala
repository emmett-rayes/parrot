package parrot
package category

import scala.annotation.targetName

/** A cartesian monoidal profunctor on an underlying category **C**.
  *
  * Represents a cartesian monoidal profunctor *P* on **C**, where
  *   - ⊗ is the categorical product
  *   - *I* is the terminal object
  *   - *π*₁: *A* ⊗ *B* ⇒ *A* is the first projection
  *   - *π*₂: *A* ⊗ *B* ⇒ *B* is the second projection
  *   - ⟨-, -⟩ is the universal pairing into the product
  *   - !: *A* ⇒ *I* is the unique morphism to the terminal object
  *   - Δ: *A* ⇒ *A* ⊗ *A* is the diagonal morphism
  */
trait Cartesian extends Monoidal {
  type Self[_, _]

  /** The unique morphism !: *A* ~> *I* to the terminal object. */
  def augment[A]: A ~> I

  /** The first projection morphism *π*₁: *A* ⊗ *B* ~> *A*. */
  def first[A, B]: (A * B) ~> A

  /** The second projection morphism *π*₂: *A* ⊗ *B* ~> *B*. */
  def second[A, B]: (A * B) ~> B

  /** Maps two morphisms *f*: *C* ~> *A* and *g*: *C* ~> *B* to the universal pairing morphism ⟨*f*, *g*⟩: *C* ~> *A* ⊗
    * *B*.
    */
  def product[C, A, B](f: C ~> A, g: C ~> B): C ~> (A * B)

  /** The tensor product of two morphisms *p* ⊗ *q* = ⟨*p* ∘ *π*₁, *q* ∘ *π*₂⟩. */
  override def tensor[A, B, C, D](p: A ~> B, q: C ~> D): (A * C) ~> (B * D) = {
    (first[A, C] >>> p) &&& (second[A, C] >>> q)
  }

  /** The left unitor morphism *λ*: *I* ⊗ *A* ~> *A* = *π*₂. */
  override def leftUnitor[A]: (I * A) ~> A = {
    second[I, A]
  }

  /** The inverse left unitor morphism *λ*⁻¹: *A* ~> *I* ⊗ *A* = ⟨!, *id*⟩. */
  override def leftUnitorInv[A]: A ~> (I * A) = {
    augment[A] &&& identity[A]
  }

  /** The right unitor morphism *ρ*: *A* ⊗ *I* ~> *A* = *π*₁. */
  override def rightUnitor[A]: (A * I) ~> A = {
    first[A, I]
  }

  /** The inverse right unitor morphism *ρ*⁻¹: *A* ~> *A* ⊗ *I* = ⟨*id*, !⟩. */
  override def rightUnitorInv[A]: A ~> (A * I) = {
    identity[A] &&& augment[A]
  }

  /** The associator morphism *α*: (*A* ⊗ *B*) ⊗ *C* ~> *A* ⊗ (*B* ⊗ *C*) = ⟨*π*₁ ∘ *π*₁, ⟨*π*₂ ∘ *π*₁, *π*₂⟩⟩. */
  override def associate[A, B, C]: ((A * B) * C) ~> (A * (B * C)) = {
    (first[A * B, C] >>> first[A, B]) &&& ((first[A * B, C] >>> second[A, B]) &&& second[A * B, C])
  }

  /** The inverse associator morphism *α*⁻¹: *A* ⊗ (*B* ⊗ *C*) ~> (*A* ⊗ *B*) ⊗ *C* = ⟨⟨*π*₁, *π*₁ ∘ *π*₂⟩, *π*₂ ∘
    * *π*₂⟩.
    */
  override def unassociate[A, B, C]: (A * (B * C)) ~> ((A * B) * C) = {
    ((first[A, B * C] &&& (second[A, B * C] >>> first[B, C])) &&& (second[A, B * C] >>> second[B, C]))
  }

  extension [C, A](f: C ~> A)
    /** Infix extension for [[product]]. */
    @targetName("productExt")
    def product[B](g: C ~> B): C ~> (A * B) = {
      Cartesian.this.product(f, g)
    }

  extension [C, A](f: C ~> A)
    /** Alias for [[product]]. */
    def &&&[B](g: C ~> B): C ~> (A * B) = {
      f.product(g)
    }

  /** The diagonal morphism Δ: *A* ~> *A* ⊗ *A*. */
  def diagonal[A]: A ~> (A * A) = {
    identity[A] &&& identity[A]
  }

  /** Laws that any `Cartesian` monoidal profunctor must satisfy. */
  object CartesianLaws {

    /** *π*₁ ∘ ⟨*f*, *g*⟩ = *f*
      */
    def firstProjection[C, A, B](
      f: C ~> A,
      g: C ~> B,
    )(using C ~> A is Eq): Boolean = {
      ((f &&& g) >>> first) === f
    }

    /** *π*₂ ∘ ⟨*f*, *g*⟩ = *g*
      */
    def secondProjection[C, A, B](
      f: C ~> A,
      g: C ~> B,
    )(using C ~> B is Eq): Boolean = {
      ((f &&& g) >>> second) === g
    }

    /** ⟨*π*₁, *π*₂⟩ = *id*
      */
    def productUniqueness[A, B](using (A * B) ~> (A * B) is Eq): Boolean = {
      (first[A, B] &&& second[A, B]) === identity[A * B]
    }

    /** For any morphism *f*: *A* ~> *I*, *f* = !
      */
    def terminalUniqueness[A](f: A ~> I)(using A ~> I is Eq): Boolean = {
      f === augment[A]
    }
  }
}

object Cartesian {

  /** Type helper to refine `I` and `Tensor` simultaneously on `Cartesian`. */
  type `with`[U, T[_, _]] = Cartesian { type I = U; type Tensor = T }

  /** Summons the `Cartesian` instance of `P`. */
  def apply[P[_, _]: Cartesian]: P is Cartesian = summon

  /** `Cartesian` instance for `Function` on the category **Type**. */
  given FunctionIsCartesian
    : (P: Function is Monoidal.`with`[Unit, [A, B] =>> (A, B)] on Function)
        => Function is Cartesian {
    export P.{
      Self as _,
      tensor as _,
      leftUnitor as _,
      leftUnitorInv as _,
      rightUnitor as _,
      rightUnitorInv as _,
      associate as _,
      unassociate as _,
      *,
    }

    def augment[A]: A => Unit = {
      _ => ()
    }

    def first[A, B]: ((A, B)) => A = {
      (a, _) => a
    }

    def second[A, B]: ((A, B)) => B = {
      (_, b) => b
    }

    def product[C, A, B](f: C => A, g: C => B): C => (A, B) = {
      c => (f(c), g(c))
    }
  }

  /** Every cartesian monoidal category induces a symmetric monoidal category, where
    *   - *β* = ⟨*π*₂, *π*₁⟩ is the braiding
    */
  given CartesianIsSymmetric: [P[_, _]] => (C: P is Cartesian) => P is Symmetric {
    export C.{
      Self as _,
      rightUnitor as _,
      rightUnitorInv as _,
      unassociate as _,
      *,
    }

    def braid[A, B]: (A * B) ~> (B * A) = {
      second &&& first
    }
  }
}
