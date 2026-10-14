package parrot
package category

import scala.compiletime.deferred

/** A **V**-valued functor on **Type**.
  *
  * Represents a functor *F*: **Type** → **V**.
  */
trait Valued {
  type Self[_]: Functor
  final type F = Self

  val SelfIsFunctor: Self is Functor = summon

  /** A typeclass describing the objects of the target category **V**. */
  type Over <: Any { type Self }
  final type V = Over

  /** Evidence that each `F[A]` is in **V**. */
  given FIsV: [A] => (F[A] is V) = deferred
}

object Valued {
  import scala.util.{Failure, Try}

  /** Refines the `Over` type of `Valued` to `T`. */
  infix type over[E <: Valued, T <: Any { type Self }] = E { type Over = T }

  /** Summons the `Valued` instance of `F`. */
  def apply[F[_]: Valued]: F is Valued = summon

  given TryIsAdditiveValued: Try is Valued {
    type Over = Monoid.Additive

    override given FIsV: [A] => (Try[A] is Monoid.Additive) = new Monoid.Additive {
      type Self = F[A]

      def zero: Try[A] = {
        Failure(Exception())
      }

      def plus(x: Try[A], y: Try[A]): Try[A] = {
        x.orElse(y)
      }
    }
  }
}
