package parrot
package category

import scala.compiletime.deferred

/** A **V**-enriched promonad on an underlying category **C**.
  *
  * Represents a promonad *P*: **C**^*op* × **C** → **Type**, where each hom-set `A ~> B` is in **V**.
  */
trait Enriched {
  type Self[_, _]: Promonad
  final type P = Self

  val SelfIsPromonad: P is Promonad = summon
  import SelfIsPromonad.*

  /** A typeclass describing the objects of the target category **V**. */
  type Over <: Any { type Self }
  final type V = Over

  /** Evidence that each hom-set `A ~> B` is in **V**. */
  given HomIsV: [A, B] => ((A ~> B) is V) = deferred

  /** Laws that any `Monoid`-enriched promonad must satisfy, where the monoid is a monoid object in a monoidal category.
    */
  object MonoidEnrichedLaws {

    /** P(f,g) ∘ η = η */
    def unitHomomorphy[A, B, C, D, K[_, _], U, T[_, _]](f: C ==> A, g: B ==> D)(
      using
      MonAB: (A ~> B) is Monoid.in[K, U, T],
      MonCD: (C ~> D) is Monoid.in[K, U, T],
      eq: K[U, C ~> D] is Eq,
    ): Boolean = {
      import MonAB.InIsPromonad.>>>
      val h = MonAB.InIsPromonad.unit(dimap(f, g))
      (MonAB.unit >>> h) === MonCD.unit
    }

    /** P(f,g) ∘ μ = μ ∘ (P(f,g) ⊗ P(f,g)) */
    def multiplicationHomomorphy[A, B, C, D, K[_, _], U, T[_, _]](f: C ==> A, g: B ==> D)(
      using
      MonAB: (A ~> B) is Monoid.in[K, U, T],
      MonCD: (C ~> D) is Monoid.in[K, U, T],
      eq: K[T[A ~> B, A ~> B], C ~> D] is Eq,
    ): Boolean = {
      import MonAB.InIsMonoidal.***
      import MonAB.InIsPromonad.>>>
      val h = MonAB.InIsPromonad.unit(dimap(f, g))
      (MonAB.multiply >>> h) === ((h *** h) >>> MonCD.multiply)
    }

    /** (- ∘ q) ∘ μ = μ ∘ ((- ∘ q) ⊗ (- ∘ q)) */
    def rightDistributivity[A, B, C, K[_, _], U, T[_, _]](q: A ~> B)(
      using
      MonBC: (B ~> C) is Monoid.in[K, U, T],
      MonAC: (A ~> C) is Monoid.in[K, U, T],
      eq: K[T[B ~> C, B ~> C], A ~> C] is Eq,
    ): Boolean = {
      import MonBC.InIsMonoidal.***
      import MonBC.InIsPromonad.>>>
      val rq = MonBC.InIsPromonad.unit((p: B ~> C) => compose(p, q))
      (MonBC.multiply >>> rq) === ((rq *** rq) >>> MonAC.multiply)
    }

    /** (p ∘ -) ∘ μ = μ ∘ ((p ∘ -) ⊗ (p ∘ -)) */
    def leftDistributivity[A, B, C, K[_, _], U, T[_, _]](p: B ~> C)(
      using
      MonAB: (A ~> B) is Monoid.in[K, U, T],
      MonAC: (A ~> C) is Monoid.in[K, U, T],
      eq: K[T[A ~> B, A ~> B], A ~> C] is Eq,
    ): Boolean = {
      import MonAB.InIsMonoidal.***
      import MonAB.InIsPromonad.>>>
      val lp = MonAB.InIsPromonad.unit((q: A ~> B) => compose(p, q))
      (MonAB.multiply >>> lp) === ((lp *** lp) >>> MonAC.multiply)
    }

    /** (p ∘ -) ∘ η = η  and  (- ∘ q) ∘ η = η */
    def unitAnnihilation[A, B, C, K[_, _], U, T[_, _]](p: B ~> C, q: A ~> B)(
      using
      MonAB: (A ~> B) is Monoid.in[K, U, T],
      MonBC: (B ~> C) is Monoid.in[K, U, T],
      MonAC: (A ~> C) is Monoid.in[K, U, T],
      eqAC: K[U, A ~> C] is Eq,
    ): Boolean = {
      import MonAC.InIsPromonad.>>>
      val lp = MonAB.InIsPromonad.unit((q1: A ~> B) => compose(p, q1))
      val rq = MonBC.InIsPromonad.unit((p1: B ~> C) => compose(p1, q))
      ((MonAB.unit >>> lp) === MonAC.unit) && ((MonBC.unit >>> rq) === MonAC.unit)
    }
  }

  /** Laws that any `Conway.Fixed`-enriched promonad must satisfy, beyond the Conway laws on each hom-set. */
  object FixedEnrichedLaws {

    /** Fixed points are dinatural across hom-sets: fix(*v* ∘ *u*) = *v*(fix(*u* ∘ *v*)) for any *u*: (*A* ~> *B*) →
      * (*C* ~> *D*) and *v*: (*C* ~> *D*) → (*A* ~> *B*), e.g. pre- and postcomposition.
      */
    def homDinaturality[A, B, C, D](u: (A ~> B) => (C ~> D), v: (C ~> D) => (A ~> B))(
      using
      FixAB: (A ~> B) is Conway.Fixed,
      FixCD: (C ~> D) is Conway.Fixed,
      eq: (A ~> B) is Eq,
    ): Boolean = {
      FixAB.fix(u.andThen(v)) === v(FixCD.fix(v.andThen(u)))
    }
  }
}

object Enriched {

  /** Refines the `Over` type of `Enriched` to `T`. */
  infix type over[E <: Enriched, T <: Any { type Self }] = E { type Over = T }

  /** Summons the `Enriched` instance of `P`. */
  def apply[P[_, _]: Enriched]: P is Enriched = summon
}
