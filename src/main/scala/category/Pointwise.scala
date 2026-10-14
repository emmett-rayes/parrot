package parrot
package category

import scala.compiletime.deferred

/** A category **V** with pointwise function types.
  *
  * Represents a category **V** where for each type *A* and object *B* in **V**, the function type *A* => *B* is in
  * **V**.
  */
trait Pointwise {

  /** A typeclass describing the objects of the category **V**. */
  type Self <: Any { type Self }
  final type V = Self

  /** Evidence that each function type `A => B` is in **V** whenever `B` is in **V**. */
  given FunctionIsV: [A, B] => (B: B is V) => ((A => B) is V) = deferred
}

object Pointwise {

  /** Summons the `Pointwise` instance of `V`. */
  def apply[V <: Any { type Self }: Pointwise]: V is Pointwise = summon

  /** `Monoid.Additive` lifts pointwise to function types. */
  given AdditiveIsPointwise: Monoid.Additive is Pointwise {
    override given FunctionIsV: [A, B] => (B: B is Monoid.Additive) => ((A => B) is Monoid.Additive) = {
      Monoid.Additive.FunctionIsAdditive[A, B]
    }
  }

  /** `Monoid.Multiplicative` lifts pointwise to function types. */
  given MultiplicativeIsPointwise: Monoid.Multiplicative is Pointwise {
    override given FunctionIsV: [A, B] => (B: B is Monoid.Multiplicative) => ((A => B) is Monoid.Multiplicative) = {
      Monoid.Multiplicative.FunctionIsMultiplicative[A, B]
    }
  }
}
