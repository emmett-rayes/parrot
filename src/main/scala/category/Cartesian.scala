package parrot
package category

import scala.annotation.targetName

/** A cartesian monoidal promonad on an underlying category **C**.
  *
  * Represents a cartesian monoidal promonad *P* on **C**, where
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

  private val Prom: Self is Promonad = summon
  import Prom.*

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

  /** The diagonal morphism Δ: *A* ~> *A* ⊗ *A*. */
  def diagonal[A]: A ~> (A * A) = {
    identity[A] &&& identity[A]
  }

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

  /** Laws that any `Cartesian` monoidal profunctor must satisfy. */
  object CartesianLaws {

    /** *π*₁ ∘ ⟨*f*, *g*⟩ = *f*
      */
    def firstProjection[A, B, C](f: A ~> B, g: A ~> C)(using (A ~> B) is Eq): Boolean = {
      ((f &&& g) >>> first) === f
    }

    /** *π*₂ ∘ ⟨*f*, *g*⟩ = *g*
      */
    def secondProjection[A, B, C](f: A ~> B, g: A ~> C)(using (A ~> C) is Eq): Boolean = {
      ((f &&& g) >>> second) === g
    }

    /** ⟨*π*₁, *π*₂⟩ = *id*
      */
    def productUniqueness[A, B](using (A * B) ~> (A * B) is Eq): Boolean = {
      (first[A, B] &&& second[A, B]) === identity[A * B]
    }

    /* *A* ~> *I*, *f* = ! */
    def terminalUniqueness[A](f: A ~> I)(using A ~> I is Eq): Boolean = {
      f === augment[A]
    }

    /** *π*₁ ∘ Δ = *id*
      */
    def diagonalFirst[A](using (A ~> A) is Eq): Boolean = {
      (diagonal[A] >>> first[A, A]) === identity[A]
    }

    /** *π*₂ ∘ Δ = *id*
      */
    def diagonalSecond[A](using (A ~> A) is Eq): Boolean = {
      (diagonal[A] >>> second[A, A]) === identity[A]
    }
  }
}

object Cartesian {

  /** Refines the `I` and `Tensor` types of `Cartesian` to `U` and `T`. */
  type `with`[U, T[_, _]] = Cartesian { type I = U; type Tensor = T }

  /** Summons the `Cartesian` instance of `P`. */
  def apply[P[_, _]: Cartesian]: P is Cartesian = summon

  /** Every object in a cartesian monoidal category is uniquely a comonoid object via the augment and diagonal. */
  given MIsComonoid: [M, P[_, _]: Promonad] => (C: P is Cartesian) => M is Comonoid {
    type In = P

    override val Mon: C.type = C

    import C.*
    import Prom.*

    def zero: M ~> I = augment

    def add: M ~> (M * M) = diagonal
  }

  /** Every cartesian monoidal category induces a symmetric monoidal category, where
    *   - *β* = ⟨*π*₂, *π*₁⟩ is the braiding
    */
  given CartesianIsSymmetric: [P[_, _]: {Promonad, Cartesian}] => (C: P is Cartesian) => P is Symmetric {
    export C.{
      Self as _,
      rightUnitor as _,
      rightUnitorInv as _,
      unassociate as _,
      *,
    }

    import C.Prom.*

    def braid[A, B]: (A * B) ~> (B * A) = {
      second &&& first
    }
  }

  /** `Cartesian` instance for `Function` on the category **Type**. */
  given FunctionIsCartesian: Function is Cartesian {
    type I      = Unit
    type Tensor = Tuple2

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

  /** `Cartesian` instance for `Function` on the category **Type** with lazy products. */
  given FunctionIsLazyCartesian: Function is Cartesian {
    type I      = Unit
    type Tensor = LazyTuple2

    def augment[A]: A => Unit = {
      _ => ()
    }

    def first[A, B]: LazyTuple2[A, B] => A = {
      p => p._1
    }

    def second[A, B]: LazyTuple2[A, B] => B = {
      p => p._2
    }

    def product[C, A, B](f: C => A, g: C => B): C => LazyTuple2[A, B] = {
      c => LazyTuple2(f(c), g(c))
    }
  }
}
