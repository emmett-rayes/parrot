package parrot
package category

import scala.compiletime.deferred

/** A **V**-valued profunctor on an underlying category **C**.
  *
  * Represents a functor *P*: **C**^*op* × **C** → **V**, where each hom-set `A ~> B` is in **V**.
  */
trait Enriched {
  type Self[_, _]: Profunctor
  final type P = Self

  /** A typeclass describing the objects of the target category **V**. */
  type Over <: Any { type Self }
  final type V = Over

  /** Evidence that each hom-set `A ~> B` is in **V**. */
  given HomIsV: [A, B] => P[A, B] is V = deferred

  /** Laws that any `Monoid`-enriched profunctor must satisfy. */
  object MonoidEnrichedLaws {
    import Monoid.in
    import Profunctor.on

    val FProm: Function is Promonad = summon
    val FMon: Function is Monoidal  = summon
    import FMon.*
    import FProm.*

    /** P(f,g) ∘ η = η */
    def unitHomomorphy[A, B, C, D](f: C => A, g: B => D)(
      using
      Prom: P is (Promonad on Function),
      MonAB: P[A, B] is (Monoid in Function) { val Mon: FMon.type },
      MonCD: P[C, D] is (Monoid in Function) { val Mon: FMon.type },
      eq: (I ~> P[C, D]) is Eq,
    ): Boolean = {
      MonAB.unit >>> Prom.dimap(f, g) === MonCD.unit
    }

    /** P(f,g)(μ) = μ ∘ (P(f,g) ⊗ P(f,g)) */
    def multiplicationHomomorphy[A, B, C, D](f: C => A, g: B => D)(
      using
      Prom: P is (Promonad on Function),
      MonAB: P[A, B] is (Monoid in Function) { val Mon: FMon.type },
      MonCD: P[C, D] is (Monoid in Function) { val Mon: FMon.type },
      eq: ((P[A, B] * P[A, B]) ~> P[C, D]) is Eq,
    ): Boolean = {
      val lhs = MonAB.multiply >>> Prom.dimap(f, g)
      val rhs = (Prom.dimap(f, g) *** Prom.dimap(f, g)) >>> MonCD.multiply
      lhs === rhs
    }
  }
}

object Enriched {

  /** Refines the `Over` type of `Enriched` to `T`. */
  infix type over[E <: Enriched, T <: Any { type Self }] = E { type Over = T }

  /** Summons the `Enriched` instance of `P`. */
  def apply[P[_, _]: Enriched]: P is Enriched = summon
}
