package parrot
package category

/** An equivalence relation on *Self*. */
trait Eq {
  type Self

  /** Returns `true` if *a* and *b* are equivalent. */
  def eq(a: Self, b: Self): Boolean

  extension (self: Self)
    /** Alias for [[eq]]. */
    def ===(other: Self): Boolean = {
      Eq.this.eq(self, other)
    }
}

object Eq {
  import scala.util.{Failure, Success, Try}

  /** Summons the `Eq` instance of `A`. */
  def apply[A: Eq]: A is Eq = summon

  /** `Eq` instance for type equality `=:=`. */
  given TypeEqIsEq: [A, B] => =:=[A, B] is Eq {
    def eq(a: A =:= B, b: A =:= B): Boolean = {
      true
    }
  }

  /** `Eq` instance for types with a `CanEqual` instance. */
  given CanEqualIsEq: [A] => CanEqual[A, A] => A is Eq {
    def eq(a: A, b: A): Boolean = {
      a == b
    }
  }

  /** `Eq` instance for `Try[A]` if `A` has an `Eq` instance. */
  given TryIsEq: [A: Eq] => Try[A] is Eq {
    def eq(a: Try[A], b: Try[A]): Boolean = {
      (a, b) match {
        case (Success(x), Success(y)) => x === y
        case (Failure(_), Failure(_)) => true
        case _                        => false
      }
    }
  }
}
