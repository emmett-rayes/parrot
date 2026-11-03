package parrot
package category

import scala.annotation.targetName

/** A classical restriction structure on a promonad *P* over a cocartesian category **C**.
  *
  * Represents a classical restriction category (Cockett–Manes) with its override operator (Lemay–Nester), where
  *   - 0: *A* → *B* is the restriction zero, the nowhere-defined arrow
  *   - *p̄*ᶜ: *A* → *A* is the complement of *p̄*, defined exactly where *p* is not
  *   - *p* ⊳ *q* = *p* ∨ *q* ∘ *p̄*ᶜ is the override, which runs *p* where it is defined and *q* elsewhere
  *   - *attempt*(*p*): *A* → *B* + *A* never fails: it tags the result of *p*, or returns the input untouched
  *
  * Definedness is decidable. The override operator is unique (Lemay and Nester, Theorem 43), and on compatible arrows
  * it is their join; for parsers, it is ordered choice. The Kleisli category of the option monad is classical; 𝒫 is
  * not, because the complement of "this program terminates" is not computable.
  *
  * @note Precomposition distributes over ⊳; postcomposition does not, since *p* ⊳ *q* commits to *p* where *p* is
  *   defined, whatever comes after.
  */
abstract class Classical(
  tracked override val promonad: Promonad,
  tracked val cocartesian: Cocartesian.On[promonad.category.type],
) extends Restriction(promonad) {
  import promonad.{P, >>>}
  import promonad.category.Obj
  import cocartesian.+

  private given TensorIsObj: [A: Obj, B: Obj] => ((A + B) is Obj) = cocartesian.tensor.objects[A, B]

  /** The restriction zero 0: *A* → *B*. */
  def zero[A: Obj, B: Obj]: P[A, B]

  /** The complement *p̄*ᶜ: *A* → *A* of *p*: *A* → *B*. */
  def complement[A: Obj, B: Obj](p: P[A, B]): P[A, A]

  /** The override *p* ⊳ *q*: *A* → *B* of *p*: *A* → *B* and *q*: *A* → *B*. */
  def orElse[A: Obj, B: Obj](p: P[A, B], q: P[A, B]): P[A, B]

  /** The attempt *attempt*(*p*): *A* → *B* + *A* of *p*: *A* → *B*. */
  def attempt[A: Obj, B: Obj](p: P[A, B]): P[A, B + A] = {
    orElse(p >>> promonad.unit(cocartesian.inl[B, A]), promonad.unit(cocartesian.inr[B, A]))
  }

  extension [A: Obj, B: Obj](p: P[A, B])
    /** Infix extension for [[orElse]]. */
    @targetName("orElseExt")
    final def |>(q: P[A, B]): P[A, B] = {
      orElse(p, q)
    }

  /** Laws that any `Classical` restriction structure must satisfy. */
  object ClassicalLaws {

    /** 0‾ = 0 */
    def zeroRestriction[A: Obj, B: Obj](using P[A, A] is Observable): Boolean = {
      restrict(zero[A, B]) =?= zero[A, A]
    }

    /** 0 ∘ *p* = 0 */
    def zeroLeft[A: Obj, B: Obj, C: Obj](p: P[A, B])(using P[A, C] is Observable): Boolean = {
      (p >>> zero[B, C]) =?= zero[A, C]
    }

    /** *p* ∘ 0 = 0 */
    def zeroRight[A: Obj, B: Obj, C: Obj](p: P[B, C])(using P[A, C] is Observable): Boolean = {
      (zero[A, B] >>> p) =?= zero[A, C]
    }

    /** 0 ⊳ *p* = *p* = *p* ⊳ 0 */
    def overrideZero[A: Obj, B: Obj](p: P[A, B])(using P[A, B] is Observable): Boolean = {
      (orElse(zero[A, B], p) =?= p) && (orElse(p, zero[A, B]) =?= p)
    }

    /** (*p* ⊳ *q*) ⊳ *r* = *p* ⊳ (*q* ⊳ *r*) (**⊳.1**)
      */
    def overrideAssociativity[A: Obj, B: Obj](p: P[A, B], q: P[A, B], r: P[A, B])(
      using P[A, B] is Observable
    ): Boolean = {
      orElse(orElse(p, q), r) =?= orElse(p, orElse(q, r))
    }

    /** *p* ⊳ (*q* ∘ *p̄*) = *p* (**⊳.2**)
      */
    def overrideRestricted[A: Obj, B: Obj](p: P[A, B], q: P[A, B])(
      using P[A, B] is Observable
    ): Boolean = {
      orElse(p, restrict(p) >>> q) =?= p
    }

    /** (*p* ∘ *q̄*) ⊳ *p* = *p* (**⊳.3**)
      */
    def overrideRestricting[A: Obj, B: Obj, C: Obj](p: P[A, B], q: P[A, C])(
      using P[A, B] is Observable
    ): Boolean = {
      orElse(restrict(q) >>> p, p) =?= p
    }

    /** (*p* ⊳ *q*) ∘ *h* = (*p* ∘ *h*) ⊳ (*q* ∘ *h*) (**⊳.4**)
      *
      * Precomposition distributes over ⊳.
      */
    def overridePrecomposition[A: Obj, B: Obj, C: Obj](
      h: P[A, B],
      p: P[B, C],
      q: P[B, C],
    )(using P[A, C] is Observable): Boolean = {
      (h >>> orElse(p, q)) =?= orElse(h >>> p, h >>> q)
    }

    /** *h* ∘ (*p* ⊳ *q*)‾ = (*h* ∘ *p̄*) ⊳ (*h* ∘ *q̄*) (**⊳.5**)
      */
    def overrideRestriction[A: Obj, B: Obj, C: Obj](
      p: P[A, B],
      q: P[A, B],
      h: P[A, C],
    )(using P[A, C] is Observable): Boolean = {
      (restrict(orElse(p, q)) >>> h) =?= orElse(restrict(p) >>> h, restrict(q) >>> h)
    }

    /** *p̄*ᶜ ∘ *p̄* = 0
      *
      * An arrow cannot be both defined and undefined.
      */
    def complementExclusion[A: Obj, B: Obj](p: P[A, B])(using P[A, A] is Observable): Boolean = {
      (restrict(p) >>> complement(p)) =?= zero[A, A]
    }

    /** *p̄* ⊳ *p̄*ᶜ = *id*
      *
      * Every input either is or is not in the domain of *p*.
      */
    def complementCover[A: Obj, B: Obj](p: P[A, B])(using P[A, A] is Observable): Boolean = {
      orElse(restrict(p), complement(p)) =?= promonad.identity[A]
    }

    /** (*p̄*ᶜ)‾ = *p̄*ᶜ
      *
      * A complement is a restriction idempotent.
      */
    def complementRestriction[A: Obj, B: Obj](p: P[A, B])(using P[A, A] is Observable): Boolean = {
      restrict(complement(p)) =?= complement(p)
    }

    /** (*p̄*ᶜ)ᶜ = *p̄* */
    def doubleComplement[A: Obj, B: Obj](p: P[A, B])(using P[A, A] is Observable): Boolean = {
      complement(complement(p)) =?= restrict(p)
    }

    /** *attempt*(*p*) = (*ι*₁ ∘ *p*) ⊳ *ι*₂
      */
    def attemptDefinition[A: Obj, B: Obj](p: P[A, B])(using P[A, B + A] is Observable): Boolean = {
      attempt(p) =?= orElse(p >>> promonad.unit(cocartesian.inl[B, A]), promonad.unit(cocartesian.inr[B, A]))
    }

    /** If *p* = *p*′ and *q* = *q*′, then *p* ⊳ *q* = *p*′ ⊳ *q*′ and *p̄*ᶜ = *p*′‾ᶜ.
      *
      * @note The premise is not checked: *p*′ and *q*′ must be equal to *p* and *q* by construction.
      */
    def congruence[A: Obj, B: Obj](p: P[A, B], p2: P[A, B], q: P[A, B], q2: P[A, B])(
      using
      P[A, B] is Observable,
      P[A, A] is Observable,
    ): Boolean = {
      (orElse(p, q) =?= orElse(p2, q2)) && (complement(p) =?= complement(p2))
    }
  }
}

object Classical {

  /** The classical restriction structures on a promonad *P*. */
  type On[P <: Promonad] = Classical { val promonad: P }
}
