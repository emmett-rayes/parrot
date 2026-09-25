package parrot
package category

import scala.compiletime.deferred

/** An enrichment over *V* on an underlying category **C**.
  *
  * Represents a functor *P*: **C**^*op* × **C** → **V**, where
  *   - each hom-set `A ~> B` is in **V**
  *   - `HomIsV` provides evidence that `A ~> B` is in **V**
  *   - `dimap` preserves the **V**-structure
  */
trait Enriched {
  type Self[_, _]: Profunctor
  final type ~>[A, B] = Self[A, B]

  /** The category **V** in which each hom-set is enriched. */
  type Over <: Any { type Self }
  final type V = Over

  /** Evidence that each hom-set `A ~> B` is in **V**. */
  given HomIsV: [A, B] => ((A ~> B) is V) = deferred
}

object Enriched {

  /** Refines the `Over` type of `Enriched` to `T`. */
  infix type over[E <: Enriched, T <: Any { type Self }] = Enriched { type Over = T }

  /** Summons the `Enriched` instance of `P`. */
  def apply[P[_, _]: Enriched]: P is Enriched = summon
}
