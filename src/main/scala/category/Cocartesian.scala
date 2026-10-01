package parrot
package category

import scala.annotation.targetName

/** A cocartesian monoidal profunctor on an underlying category **C**.
  *
  * Represents a cocartesian monoidal profunctor *P* on **C**, where
  *   - ⊕ is the categorical coproduct
  *   - *Z* is the initial object
  *   - *ι*₁: *A* ⇒ *A* ⊕ *B* is the left injection
  *   - *ι*₂: *B* ⇒ *A* ⊕ *B* is the right injection
  *   - [-, -] is the universal copairing from the coproduct
  *   - ¡: *Z* ⇒ *A* is the unique morphism from the initial object
  *   - ∇: *A* ⊕ *A* ⇒ *A* is the fold morphism
  */
trait Cocartesian extends Monoidal {
  type Self[_, _]

  /** The initial object *Z* in *Ob*(**C**). */
  type Z
  override type I = Z

  /** The coproduct ⊕ on objects. */
  final type +[A, B] = Tensor[A, B]

  private val Prom: Self is Promonad = summon
  import Prom.*

  /** The unique morphism ¡: *Z* ~> *A* from the initial object. */
  def absurd[A]: Z ~> A

  /** The left injection morphism *ι*₁: *A* ~> *A* ⊕ *B*. */
  def left[A, B]: A ~> (A + B)

  /** The right injection morphism *ι*₂: *B* ~> *A* ⊕ *B*. */
  def right[A, B]: B ~> (A + B)

  /** Maps two morphisms *f*: *A* ~> *C* and *g*: *B* ~> *C* to the universal copairing morphism [*f*, *g*]: *A* ⊕ *B*
    * ~> *C*.
    */
  def sum[A, B, C](f: A ~> C, g: B ~> C): (A + B) ~> C

  /** The tensor product of two morphisms *p* ⊕ *q* = [*p* ∘ *ι*₁, *q* ∘ *ι*₂]. */
  override def tensor[A, B, C, D](p: A ~> B, q: C ~> D): (A + C) ~> (B + D) = {
    (p >>> left[B, D]) ||| (q >>> right[B, D])
  }

  /** The left unitor morphism *λ*: *Z* ⊕ *A* ~> *A* = [¡, *id*]. */
  override def leftUnitor[A]: (Z + A) ~> A = {
    absurd[A] ||| identity[A]
  }

  /** The inverse left unitor morphism *λ*⁻¹: *A* ~> *Z* ⊕ *A* = *ι*₂. */
  override def leftUnitorInv[A]: A ~> (Z + A) = {
    right[Z, A]
  }

  /** The right unitor morphism *ρ*: *A* ⊕ *Z* ~> *A* = [*id*, ¡]. */
  override def rightUnitor[A]: (A + Z) ~> A = {
    identity[A] ||| absurd[A]
  }

  /** The inverse right unitor morphism *ρ*⁻¹: *A* ~> *A* ⊕ *Z* = *ι*₁. */
  override def rightUnitorInv[A]: A ~> (A + Z) = {
    left[A, Z]
  }

  /** The associator morphism *α*: (*A* ⊕ *B*) ⊕ *C* ~> *A* ⊕ (*B* ⊕ *C*) = [[*ι*₁, *ι*₁ ∘ *ι*₂], *ι*₂ ∘ *ι*₂]. */
  override def associate[A, B, C]: ((A + B) + C) ~> (A + (B + C)) = {
    (left[A, B + C] ||| (left[B, C] >>> right[A, B + C])) ||| (right[B, C] >>> right[A, B + C])
  }

  /** The inverse associator morphism *α*⁻¹: *A* ⊕ (*B* ⊕ *C*) ~> (*A* ⊕ *B*) ⊕ *C* = [*ι*₁ ∘ *ι*₁, [*ι*₂ ∘ *ι*₁,
    * *ι*₂]].
    */
  override def unassociate[A, B, C]: (A + (B + C)) ~> ((A + B) + C) = {
    (left[A, B] >>> left[A + B, C]) ||| ((right[A, B] >>> left[A + B, C]) ||| right[A + B, C])
  }

  extension [A, C](f: A ~> C)
    /** Infix extension for [[sum]]. */
    @targetName("sumExt")
    def sum[B](g: B ~> C): (A + B) ~> C = {
      Cocartesian.this.sum(f, g)
    }

  extension [A, C](f: A ~> C)
    /** Alias for [[sum]]. */
    def |||[B](g: B ~> C): (A + B) ~> C = {
      f.sum(g)
    }

  /** The fold (codiagonal) morphism ∇: *A* ⊕ *A* ~> *A*. */
  def fold[A]: (A + A) ~> A = {
    identity[A] ||| identity[A]
  }

  /** Laws that any `Cocartesian` monoidal profunctor must satisfy. */
  object CocartesianLaws {

    /** [*f*, *g*] ∘ *ι*₁ = *f*
      */
    def leftInjection[A, B, C](f: A ~> C, g: B ~> C)(using (A ~> C) is Eq): Boolean = {
      (left[A, B] >>> (f ||| g)) === f
    }

    /** [*f*, *g*] ∘ *ι*₂ = *g*
      */
    def rightInjection[A, B, C](f: A ~> C, g: B ~> C)(using (B ~> C) is Eq): Boolean = {
      (right[A, B] >>> (f ||| g)) === g
    }

    /** [*ι*₁, *ι*₂] = *id*
      */
    def sumUniqueness[A, B](using (A + B) ~> (A + B) is Eq): Boolean = {
      (left[A, B] ||| right[A, B]) === identity[A + B]
    }

    /* *Z* ~> *A*, *f* = ¡ */
    def initialUniqueness[A](f: Z ~> A)(using (Z ~> A) is Eq): Boolean = {
      f === absurd[A]
    }

    /** ∇ ∘ *ι*₁ = *id*
      */
    def foldLeft[A](using (A ~> A) is Eq): Boolean = {
      (left[A, A] >>> fold[A]) === identity[A]
    }

    /** ∇ ∘ *ι*₂ = *id*
      */
    def foldRight[A](using (A ~> A) is Eq): Boolean = {
      (right[A, A] >>> fold[A]) === identity[A]
    }
  }
}

object Cocartesian {

  /** Refines the `Z` and `Tensor` types of `Cocartesian` to `U` and `T`. */
  type `with`[U, T[_, _]] = Cocartesian { type Z = U; type Tensor = T }

  /** Summons the `Cocartesian` instance of `P`. */
  def apply[P[_, _]: Cocartesian]: P is Cocartesian = summon

  /** Every object in a cocartesian monoidal category is uniquely a monoid object via the initial morphism and fold. */
  given MIsMonoid: [M, P[_, _]: Promonad] => (C: P is Cocartesian) => M is Monoid {
    type In = P

    override val Mon: C.type = C

    import C.*
    import Prom.*

    def unit: Z ~> M = absurd

    def multiply: (M + M) ~> M = fold
  }

  /** Every cocartesian monoidal category induces a symmetric monoidal category, where
    *   - *β* = [*ι*₂, *ι*₁] is the braiding
    */
  given CocartesianIsSymmetric: [P[_, _]: Promonad] => (C: P is Cocartesian) => P is Symmetric {
    export C.{
      Self as _,
      rightUnitor as _,
      rightUnitorInv as _,
      unassociate as _,
      *,
    }

    import C.Prom.*

    def braid[A, B]: (A * B) ~> (B * A) = {
      right[B, A] ||| left[B, A]
    }
  }

  /** `Cocartesian` instance for `Function` on the category **Type**. */
  given FunctionIsCocartesian: Function is Cocartesian {
    type Z      = Nothing
    type Tensor = Either

    def absurd[A]: Nothing => A = {
      n => n
    }

    def left[A, B]: A => Either[A, B] = {
      Left(_)
    }

    def right[A, B]: B => Either[A, B] = {
      Right(_)
    }

    def sum[A, B, C](f: A => C, g: B => C): Either[A, B] => C = {
      _.fold(f, g)
    }
  }
}
