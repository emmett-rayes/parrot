package parrot
package category

import scala.annotation.targetName

/** A restriction structure on a promonad *P*.
  *
  * Represents a restriction category (Cockett–Lack), where
  *   - *p̄*: *A* → *A* is the restriction of *p*: *A* → *B*
  *   - *p* is total when *p̄* = *id*
  *   - the pure arrows *η*(*f*) are total
  *
  * Every arrow knows where it is defined, as an arrow of *P* itself. In 𝒫, *p̄* runs *p* and returns its input; in the
  * Kleisli category of the option monad, it succeeds where *p* succeeds. For parsers, *p̄* is positive lookahead.
  */
abstract class Restriction(tracked val promonad: Promonad) extends caps.Pure {
  import promonad.{P, >>>}
  import promonad.category.{Obj, -->}

  /** The restriction *p̄*: *A* → *A* of *p*: *A* → *B*.
    *
    * This is the partial identity on the inputs where *p* is defined.
    */
  def restrict[A: Obj, B: Obj](p: P[A, B]): P[A, A]

  extension [A: Obj, B: Obj](p: P[A, B])
    /** Postfix form of [[restrict]]. */
    @targetName("restrictExt")
    final def restricted: P[A, A] = {
      restrict(p)
    }

  /** Laws that any `Restriction` must satisfy. */
  object RestrictionLaws {

    /** *p* ∘ *p̄* = *p* (**R1**)
      */
    def r1[A: Obj, B: Obj](p: P[A, B])(using P[A, B] is Observable): Boolean = {
      (restrict(p) >>> p) =?= p
    }

    /** *q̄* ∘ *p̄* = *p̄* ∘ *q̄* (**R2**)
      */
    def r2[A: Obj, B: Obj, C: Obj](p: P[A, B], q: P[A, C])(
      using P[A, A] is Observable
    ): Boolean = {
      (restrict(p) >>> restrict(q)) =?= (restrict(q) >>> restrict(p))
    }

    /** (*q* ∘ *p̄*)‾ = *q̄* ∘ *p̄* (**R3**)
      */
    def r3[A: Obj, B: Obj, C: Obj](p: P[A, B], q: P[A, C])(
      using P[A, A] is Observable
    ): Boolean = {
      restrict(restrict(p) >>> q) =?= (restrict(p) >>> restrict(q))
    }

    /** *q̄* ∘ *p* = *p* ∘ (*q* ∘ *p*)‾ (**R4**)
      */
    def r4[A: Obj, B: Obj, C: Obj](p: P[A, B], q: P[B, C])(
      using P[A, B] is Observable
    ): Boolean = {
      (p >>> restrict(q)) =?= (restrict(p >>> q) >>> p)
    }

    /** *η*(*f*)‾ = *id*
      *
      * Pure arrows are total.
      */
    def pureTotal[A: Obj, B: Obj](f: A --> B)(using P[A, A] is Observable): Boolean = {
      restrict(promonad.unit(f)) =?= promonad.identity[A]
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

object Restriction {

  /** The restriction structures on a promonad *P*. */
  type On[P <: Promonad] = Restriction { val promonad: P }
}
