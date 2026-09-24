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
}
