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

  val Prom: P is Promonad = summon
  import Prom.*

  /** A typeclass describing the objects of the target category **V**. */
  type Over <: Any { type Self }
  final type V = Over

  /** Evidence that each hom-set `A ~> B` is in **V**. */
  given HomIsV: [A, B] => ((A ~> B) is V) = deferred

  /** Laws that any `Monoid`-enriched promonad must satisfy, where the monoid is a monoid object in a monoidal category.
    */
  object MonoidEnrichedLaws {
    import Monoid.in
    import Profunctor.on

    /** Refines `Monoid` to have monoidal category `K` with unit `U` and tensor `T`. */
    type MonoidIn[K[_, _], U, T[_, _]] = (Monoid in K) {
      val Prom: K is (Promonad on Function)
      val Mon: K is Monoidal.`with`[U, T]
    }

    /** P(f,g) ∘ η = η */
    def unitHomomorphy[A, B, C, D, K[_, _], U, T[_, _]](f: C ==> A, g: B ==> D)(
      using
      MonAB: (A ~> B) is MonoidIn[K, U, T],
      MonCD: (C ~> D) is MonoidIn[K, U, T],
      eq: K[U, C ~> D] is Eq,
    ): Boolean = {
      import MonAB.Prom.>>>
      val h = MonAB.Prom.unit(dimap(f, g))
      (MonAB.unit >>> h) === MonCD.unit
    }

    /** P(f,g) ∘ μ = μ ∘ (P(f,g) ⊗ P(f,g)) */
    def multiplicationHomomorphy[A, B, C, D, K[_, _], U, T[_, _]](f: C ==> A, g: B ==> D)(
      using
      MonAB: (A ~> B) is MonoidIn[K, U, T],
      MonCD: (C ~> D) is MonoidIn[K, U, T],
      eq: K[T[A ~> B, A ~> B], C ~> D] is Eq,
    ): Boolean = {
      import MonAB.Mon.***
      import MonAB.Prom.>>>
      val h = MonAB.Prom.unit(dimap(f, g))
      (MonAB.multiply >>> h) === ((h *** h) >>> MonCD.multiply)
    }

    /** (- ∘ q) ∘ μ = μ ∘ ((- ∘ q) ⊗ (- ∘ q)) */
    def rightDistributivity[A, B, C, K[_, _], U, T[_, _]](q: A ~> B)(
      using
      MonBC: (B ~> C) is MonoidIn[K, U, T],
      MonAC: (A ~> C) is MonoidIn[K, U, T],
      eq: K[T[B ~> C, B ~> C], A ~> C] is Eq,
    ): Boolean = {
      import MonBC.Mon.***
      import MonBC.Prom.>>>
      val rq = MonBC.Prom.unit((p: B ~> C) => compose(p, q))
      (MonBC.multiply >>> rq) === ((rq *** rq) >>> MonAC.multiply)
    }

    /** (p ∘ -) ∘ μ = μ ∘ ((p ∘ -) ⊗ (p ∘ -)) */
    def leftDistributivity[A, B, C, K[_, _], U, T[_, _]](p: B ~> C)(
      using
      MonAB: (A ~> B) is MonoidIn[K, U, T],
      MonAC: (A ~> C) is MonoidIn[K, U, T],
      eq: K[T[A ~> B, A ~> B], A ~> C] is Eq,
    ): Boolean = {
      import MonAB.Mon.***
      import MonAB.Prom.>>>
      val lp = MonAB.Prom.unit((q: A ~> B) => compose(p, q))
      (MonAB.multiply >>> lp) === ((lp *** lp) >>> MonAC.multiply)
    }

    /** (p ∘ -) ∘ η = η  and  (- ∘ q) ∘ η = η */
    def unitAnnihilation[A, B, C, K[_, _], U, T[_, _]](p: B ~> C, q: A ~> B)(
      using
      MonAB: (A ~> B) is MonoidIn[K, U, T],
      MonBC: (B ~> C) is MonoidIn[K, U, T],
      MonAC: (A ~> C) is MonoidIn[K, U, T],
      eqAC: K[U, A ~> C] is Eq,
    ): Boolean = {
      import MonAC.Prom.>>>
      val lp = MonAB.Prom.unit((q1: A ~> B) => compose(p, q1))
      val rq = MonBC.Prom.unit((p1: B ~> C) => compose(p1, q))
      ((MonAB.unit >>> lp) === MonAC.unit) && ((MonBC.unit >>> rq) === MonAC.unit)
    }
  }
}

object Enriched {

  /** Refines the `Over` type of `Enriched` to `T`. */
  infix type over[E <: Enriched, T <: Any { type Self }] = E { type Over = T }

  /** Summons the `Enriched` instance of `P`. */
  def apply[P[_, _]: Enriched]: P is Enriched = summon
}
