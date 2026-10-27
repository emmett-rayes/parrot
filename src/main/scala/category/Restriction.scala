package parrot
package category

import scala.annotation.targetName

/** A restriction structure on a promonad *P*: every arrow knows where it is defined, as an arrow of *P* itself.
  *
  * Represents a restriction category (Cockett–Lack), where
  *   - *p̄*: *A* → *A*, the restriction of *p*: *A* → *B*, is the partial identity on the inputs where *p* is defined
  *   - *p* is total when *p̄* = *id*; the pure arrows *unit*(*f*) are total
  *
  * In 𝒫, *p̄* runs *p* and returns its input; in the Kleisli category of `Option`, it succeeds where *p* succeeds. For
  * parsers, *p̄* is positive lookahead.
  */
abstract class Restriction(tracked val P: Promonad) extends caps.Pure {
  import P.P
  import P.K.{Obj, -->}

  /** The restriction *p̄*: *A* → *A* of *p*: *A* → *B*. */
  def restrict[A: Obj, B: Obj](p: P[A, B]): P[A, A]

  extension [A: Obj, B: Obj](p: P[A, B])
    /** Postfix form of [[restrict]]. */
    @targetName("restrictExt")
    final def restricted: P[A, A] = {
      restrict(p)
    }

  /** Laws that any `Restriction` must satisfy: the four axioms of Cockett and Lack, written diagrammatically. */
  object RestrictionLaws {

    /** **R1** *p̄* ⨾ *p* = *p*
      */
    def r1[A: Obj, B: Obj](p: P[A, B])(using P[A, B] is Observable): Boolean = {
      P.multiply(p, restrict(p)) =?= p
    }

    /** **R2** *p̄* ⨾ *q̄* = *q̄* ⨾ *p̄*
      */
    def r2[A: Obj, B: Obj, C: Obj](p: P[A, B], q: P[A, C])(
      using P[A, A] is Observable
    ): Boolean = {
      P.multiply(restrict(q), restrict(p)) =?= P.multiply(restrict(p), restrict(q))
    }

    /** **R3** (*p̄* ⨾ *q*)‾ = *p̄* ⨾ *q̄*
      */
    def r3[A: Obj, B: Obj, C: Obj](p: P[A, B], q: P[A, C])(
      using P[A, A] is Observable
    ): Boolean = {
      restrict(P.multiply(q, restrict(p))) =?= P.multiply(restrict(q), restrict(p))
    }

    /** **R4** *p* ⨾ *q̄* = (*p* ⨾ *q*)‾ ⨾ *p*
      */
    def r4[A: Obj, B: Obj, C: Obj](p: P[A, B], q: P[B, C])(
      using P[A, B] is Observable
    ): Boolean = {
      P.multiply(restrict(q), p) =?= P.multiply(p, restrict(P.multiply(q, p)))
    }

    /** *unit*(*f*)‾ = *id*: pure arrows are total.
      */
    def pureTotal[A: Obj, B: Obj](f: A --> B)(using P[A, A] is Observable): Boolean = {
      restrict(P.unit(f)) =?= P.identity[A]
    }

    /** If *p* = *p*′, then *p̄* = *p*′‾.
      *
      * @note The premise is not checked: *p*′ must be equal to *p* by construction.
      */
    def congruence[A: Obj, B: Obj](p: P[A, B], p2: P[A, B])(
      using P[A, A] is Observable
    ): Boolean = {
      restrict(p) =?= restrict(p2)
    }
  }
}

/** A classical restriction structure on a promonad *P* whose base has coproducts: definedness is decidable.
  *
  * Represents a classical restriction category (Cockett–Manes) with its override operator, where
  *   - 0: *A* → *B* is the nowhere-defined arrow, the restriction zero
  *   - *p̄*ᶜ: *A* → *A* is the complement of *p̄*: defined exactly where *p* is not
  *   - *p* ⊳ *q* = *p* ∨ *p̄*ᶜ ⨾ *q* runs *p* where it is defined and *q* elsewhere: override, i.e. ordered choice
  *   - *attempt*(*p*): *A* → *B* + *A* = (*p* ⨾ *ι*₁) ⊳ *ι*₂ never fails: it tags the result of *p*, or returns the
  *     input untouched
  *
  * In a classical restriction category the override operator is unique (Lemay and Nester, Theorem 43), and on
  * compatible arrows it is their join. Precomposition distributes over ⊳; postcomposition does not, since *p* ⊳ *q*
  * commits to *p* where *p* is defined, whatever comes after. The Kleisli category of `Option` is classical; 𝒫 is not,
  * because the complement of "this program terminates" is not computable.
  */
abstract class Classical(tracked override val P: Promonad, tracked val C: Cocartesian { val K: P.K.type })
    extends Restriction(P) {
  import C.{+, given}
  import P.P
  import P.K.Obj

  /** The restriction zero 0: *A* → *B*, defined nowhere. */
  def zero[A: Obj, B: Obj]: P[A, B]

  /** The complement *p̄*ᶜ: *A* → *A*: the identity where *p* is undefined, undefined where it is defined. */
  def complement[A: Obj, B: Obj](p: P[A, B]): P[A, A]

  /** Override *p* ⊳ *q*: *p* where *p* is defined, *q* elsewhere. */
  def orElse[A: Obj, B: Obj](p: P[A, B], q: P[A, B]): P[A, B]

  /** *attempt*(*p*) = (*p* ⨾ *ι*₁) ⊳ *ι*₂: the result of *p* on the left, or the untouched input on the right.
    */
  def attempt[A: Obj, B: Obj](p: P[A, B]): P[A, B + A] = {
    orElse(P.multiply(P.unit(C.inl[B, A]), p), P.unit(C.inr[B, A]))
  }

  extension [A: Obj, B: Obj](p: P[A, B])
    /** Infix form of [[orElse]]: *p* ⊳ *q*. */
    @targetName("orElseExt")
    final def |>(q: P[A, B]): P[A, B] = {
      orElse(p, q)
    }

  /** Laws that any `Classical` restriction structure must satisfy. The override laws are those of Lemay and Nester,
    * with composition written diagrammatically.
    */
  object ClassicalLaws {

    /** 0‾ = 0 */
    def zeroRestriction[A: Obj, B: Obj](using P[A, A] is Observable): Boolean = {
      restrict(zero[A, B]) =?= zero[A, A]
    }

    /** 0 ⨾ *p* = 0 */
    def zeroLeft[A: Obj, B: Obj, C: Obj](p: P[B, C])(using P[A, C] is Observable): Boolean = {
      P.multiply(p, zero[A, B]) =?= zero[A, C]
    }

    /** *p* ⨾ 0 = 0
      */
    def zeroRight[A: Obj, B: Obj, C: Obj](p: P[A, B])(using P[A, C] is Observable): Boolean = {
      P.multiply(zero[B, C], p) =?= zero[A, C]
    }

    /** 0 ⊳ *p* = *p* = *p* ⊳ 0 */
    def overrideZero[A: Obj, B: Obj](p: P[A, B])(using P[A, B] is Observable): Boolean = {
      (orElse(zero[A, B], p) =?= p) && (orElse(p, zero[A, B]) =?= p)
    }

    /** **⊳.1** (*p* ⊳ *q*) ⊳ *r* = *p* ⊳ (*q* ⊳ *r*)
      */
    def overrideAssociativity[A: Obj, B: Obj](p: P[A, B], q: P[A, B], r: P[A, B])(
      using P[A, B] is Observable
    ): Boolean = {
      orElse(orElse(p, q), r) =?= orElse(p, orElse(q, r))
    }

    /** **⊳.2** *p* ⊳ (*p̄* ⨾ *q*) = *p*
      */
    def overrideRestricted[A: Obj, B: Obj](p: P[A, B], q: P[A, B])(
      using P[A, B] is Observable
    ): Boolean = {
      orElse(p, P.multiply(q, restrict(p))) =?= p
    }

    /** **⊳.3** (*q̄* ⨾ *p*) ⊳ *p* = *p*
      */
    def overrideRestricting[A: Obj, B: Obj, C: Obj](p: P[A, B], q: P[A, C])(
      using P[A, B] is Observable
    ): Boolean = {
      orElse(P.multiply(p, restrict(q)), p) =?= p
    }

    /** **⊳.4** *h* ⨾ (*p* ⊳ *q*) = (*h* ⨾ *p*) ⊳ (*h* ⨾ *q*): precomposition distributes.
      */
    def overridePrecomposition[A: Obj, B: Obj, C: Obj](
      h: P[A, B],
      p: P[B, C],
      q: P[B, C],
    )(using P[A, C] is Observable): Boolean = {
      P.multiply(orElse(p, q), h) =?= orElse(P.multiply(p, h), P.multiply(q, h))
    }

    /** **⊳.5** (*p* ⊳ *q*)‾ ⨾ *h* = (*p̄* ⨾ *h*) ⊳ (*q̄* ⨾ *h*)
      */
    def overrideRestriction[A: Obj, B: Obj, C: Obj](
      p: P[A, B],
      q: P[A, B],
      h: P[A, C],
    )(using P[A, C] is Observable): Boolean = {
      P.multiply(h, restrict(orElse(p, q))) =?= orElse(P.multiply(h, restrict(p)), P.multiply(h, restrict(q)))
    }

    /** *p̄* ⨾ *p̄*ᶜ = 0: an arrow cannot be both defined and undefined.
      */
    def complementExclusion[A: Obj, B: Obj](p: P[A, B])(using P[A, A] is Observable): Boolean = {
      P.multiply(complement(p), restrict(p)) =?= zero[A, A]
    }

    /** *p̄* ⊳ *p̄*ᶜ = *id*: every input either is or is not in the domain of *p*.
      */
    def complementCover[A: Obj, B: Obj](p: P[A, B])(using P[A, A] is Observable): Boolean = {
      orElse(restrict(p), complement(p)) =?= P.identity[A]
    }

    /** (*p̄*ᶜ)‾ = *p̄*ᶜ: a complement is a restriction idempotent. */
    def complementRestriction[A: Obj, B: Obj](p: P[A, B])(using P[A, A] is Observable): Boolean = {
      restrict(complement(p)) =?= complement(p)
    }

    /** (*p̄*ᶜ)ᶜ = *p̄* */
    def doubleComplement[A: Obj, B: Obj](p: P[A, B])(using P[A, A] is Observable): Boolean = {
      complement(complement(p)) =?= restrict(p)
    }

    /** *attempt*(*p*) = (*p* ⨾ *ι*₁) ⊳ *ι*₂
      */
    def attemptDefinition[A: Obj, B: Obj](p: P[A, B])(using P[A, B + A] is Observable): Boolean = {
      attempt(p) =?= orElse(P.multiply(P.unit(C.inl[B, A]), p), P.unit(C.inr[B, A]))
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
