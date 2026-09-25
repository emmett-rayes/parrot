package parrot
package category

import scala.annotation.targetName

/** A monoidal profunctor on an underlying category **C**.
  *
  * Represents a monoidal profunctor *P* on **C**, where
  *   - ⊗ is the tensor product
  *   - *I* is the unit object
  *   - *α*: (*A* ⊗ *B*) ⊗ *C* ⇒ *A* ⊗ (*B* ⊗ *C*) is the associator
  *   - *λ*: *I* ⊗ *A* ⇒ *A* is the left unitor
  *   - *ρ*: *A* ⊗ *I* ⇒ *A* is the right unitor
  */
trait Monoidal {
  type Self[_, _]: Promonad

  private val Prom: Self is Promonad = summon
  import Prom.*

  /** The unit object *I* in *Ob*(**C**). */
  type I

  /** The tensor product ⊗ on objects. */
  type Tensor[_, _]
  final type * = Tensor

  /** Maps two morphisms *p*: *A* ~> *B* and *q*: *C* ~> *D* to a morphism *p* ⊗ *q*: *A* ⊗ *C* ~> *B* ⊗ *D* in the
    * category induced by *P*.
    */
  def tensor[A, B, C, D](p: A ~> B, q: C ~> D): (A * C) ~> (B * D)

  /** The left unitor morphism *λ*: *I* ⊗ *A* ~> *A*. */
  def leftUnitor[A]: (I * A) ~> A

  /** The inverse left unitor morphism *λ*⁻¹: *A* ~> *I* ⊗ *A*. */
  def leftUnitorInv[A]: A ~> (I * A)

  /** The right unitor morphism *ρ*: *A* ⊗ *I* ~> *A*. */
  def rightUnitor[A]: (A * I) ~> A

  /** The inverse right unitor morphism *ρ*⁻¹: *A* ~> *A* ⊗ *I*. */
  def rightUnitorInv[A]: A ~> (A * I)

  /** The associator morphism *α*: (*A* ⊗ *B*) ⊗ *C* ~> *A* ⊗ (*B* ⊗ *C*) = ((A * B) * C) ~> (A * (B * C)). */
  def associate[A, B, C]: ((A * B) * C) ~> (A * (B * C))

  /** The inverse associator morphism *α*⁻¹: *A* ⊗ (*B* ⊗ *C*) ~> (*A* ⊗ *B*) ⊗ *C*. */
  def unassociate[A, B, C]: (A * (B * C)) ~> ((A * B) * C)

  extension [A, B](p: A ~> B)
    /** Infix extension for [[tensor]]. */
    @targetName("tensorExt")
    infix def tensor[C, D](q: C ~> D): (A * C) ~> (B * D) = {
      Monoidal.this.tensor(p, q)
    }

  extension [A, B](p: A ~> B)
    /** Alias for [[tensor]]. */
    def ***[C, D](q: C ~> D): (A * C) ~> (B * D) = {
      p.tensor(q)
    }

  /** Laws that any `Monoidal` must satisfy. */
  object MonoidalLaws {

    /** *id* ⊗ *id* = *id*
      */
    def tensorIdentity[A, B](using (A * B) ~> (A * B) is Eq): Boolean = {
      (identity[A] *** identity[B]) === identity[A * B]
    }

    /** (*f2* ∘ *f1*) ⊗ (*g2* ∘ *g1*) = (*f2* ⊗ *g2*) ∘ (*f1* ⊗ *g1*)
      */
    def tensorComposition[A, B, C, D, E, F](
      f1: A ~> B,
      f2: B ~> C,
      g1: D ~> E,
      g2: E ~> F,
    )(using (A * D) ~> (C * F) is Eq): Boolean = {
      ((f1 >>> f2) *** (g1 >>> g2)) === ((f1 *** g1) >>> (f2 *** g2))
    }

    /** (*f* ⊗ (*g* ⊗ *h*)) ∘ *α* = *α* ∘ ((*f* ⊗ *g*) ⊗ *h*)
      */
    def associatorNaturality[A1, A2, B1, B2, C1, C2](
      f: A1 ~> A2,
      g: B1 ~> B2,
      h: C1 ~> C2,
    )(using ((A1 * B1) * C1) ~> (A2 * (B2 * C2)) is Eq): Boolean = {
      (associate[A1, B1, C1] >>> (f *** (g *** h))) === (((f *** g) *** h) >>> associate[A2, B2, C2])
    }

    /** *f* ∘ *λ* = *λ* ∘ (*id* ⊗ *f*)
      */
    def leftUnitorNaturality[A, B](f: A ~> B)(using (I * A) ~> B is Eq): Boolean = {
      (leftUnitor[A] >>> f) === ((identity[I] *** f) >>> leftUnitor[B])
    }

    /** *f* ∘ *ρ* = *ρ* ∘ (*f* ⊗ *id*)
      */
    def rightUnitorNaturality[A, B](f: A ~> B)(using (A * I) ~> B is Eq): Boolean = {
      (rightUnitor[A] >>> f) === ((f *** identity[I]) >>> rightUnitor[B])
    }

    /** (*id* ⊗ *λ*) ∘ *α* = *ρ* ⊗ *id*
      */
    def triangle[A, B](using ((A * I) * B) ~> (A * B) is Eq): Boolean = {
      val lhs = associate[A, I, B] >>> (identity[A] *** leftUnitor[B])
      val rhs = rightUnitor[A] *** identity[B]
      lhs === rhs
    }

    /** (*id* ⊗ *α*) ∘ *α* ∘ (*α* ⊗ *id*) = *α* ∘ *α*
      */
    def pentagon[A, B, C, D](using (((A * B) * C) * D) ~> (A * (B * (C * D))) is Eq): Boolean = {
      val lhs = (associate[A, B, C] *** identity[D]) >>> associate[A, B * C, D] >>> (identity[A] *** associate[B, C, D])
      val rhs = associate[A * B, C, D] >>> associate[A, B, C * D]
      lhs === rhs
    }
  }
}

object Monoidal {

  /** Type helper to refine `I` and `Tensor` simultaneously on `Monoidal`. */
  type `with`[U, T[_, _]] = Monoidal { type I = U; type Tensor = T }

  /** Summons the `Monoidal` instance of `P`. */
  def apply[P[_, _]: Monoidal]: P is Monoidal = summon

  /** `Monoidal` instance for `Function` on the category **Type**. */
  given FunctionIsMonoidal: Function is Monoidal {
    type I      = Unit
    type Tensor = [A, B] =>> (A, B)

    def tensor[A, B, C, D](p: A => B, q: C => D): ((A, C)) => (B, D) = {
      (a, c) => (p(a), q(c))
    }

    def leftUnitor[A]: ((Unit, A)) => A = {
      (_, a) => a
    }

    def leftUnitorInv[A]: A => (Unit, A) = {
      a => ((), a)
    }

    def rightUnitor[A]: ((A, Unit)) => A = {
      (a, _) => a
    }

    def rightUnitorInv[A]: A => (A, Unit) = {
      a => (a, ())
    }

    def associate[A, B, C]: (((A, B), C)) => (A, (B, C)) = {
      case ((a, b), c) => (a, (b, c))
    }

    def unassociate[A, B, C]: ((A, (B, C))) => ((A, B), C) = {
      case (a, (b, c)) => ((a, b), c)
    }
  }
}
