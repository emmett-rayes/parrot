package parrot
package category

import scala.annotation.targetName

/** A monoid with an additive "+" flavor.
  *
  * Represents an algebraic monoid (*M*, +, 0), where
  *   - 0: *M* is the identity element
  *   - +: *M* × *M* → *M* is the associative binary operation
  */
trait `Monoid+` {
  type Self
  type M = Self

  /** The unit element 0 of *M*. */
  def zero: M

  /** Combines two elements in *M*. */
  def plus(x: M, y: M): M

  extension (x: M)
    /** Infix extension for [[plus]]. */
    @targetName("plusExt")
    def plus(y: M): M = {
      `Monoid+`.this.plus(x, y)
    }

  extension (x: M)
    /** Alias for [[plus]]. */
    def <+>(y: M): M = {
      x.plus(y)
    }

  /** Laws that any `Monoid+` must satisfy. */
  object `Monoid+Laws` {

    /** 0 + *x* = *x* */
    def leftIdentity(x: M)(using M is Eq): Boolean = {
      (zero <+> x) === x
    }

    /** *x* + 0 = *x*
      */
    def rightIdentity(x: M)(using M is Eq): Boolean = {
      (x <+> zero) === x
    }

    /** (*x* + *y*) + *z* = *x* + (*y* + *z*) */
    def associativity(x: M, y: M, z: M)(using M is Eq): Boolean = {
      ((x <+> y) <+> z) === (x <+> (y <+> z))
    }
  }
}

object `Monoid+` {
  import scala.util.{Failure, Try}

  /** Summons the `Monoid+` instance of `M`. */
  def apply[M: `Monoid+`]: M is `Monoid+` = summon

  /** `Option[A]` is a `Monoid+` under `orElse` with `None` as zero. */
  given `OptionIsMonoid+`: [A] => Option[A] is `Monoid+` {
    def zero: Option[A] = {
      None
    }

    def plus(x: Option[A], y: Option[A]): Option[A] = {
      x.orElse(y)
    }
  }

  /** `Try[A]` is a `Monoid+` under `orElse` with `Failure` as zero. */
  given `TryIsMonoid+`: [A] => Try[A] is `Monoid+` {
    def zero: Try[A] = {
      Failure(Exception())
    }

    def plus(x: Try[A], y: Try[A]): Try[A] = {
      x.orElse(y)
    }
  }

  /** `A => B` is a `Monoid+` if `B` is a `Monoid+`. */
  given FunctionIsMonoidPlus: [A, B: `Monoid+`] => Function[A, B] is `Monoid+` {
    def zero: A => B = {
      _ => B.zero
    }

    def plus(f: A => B, g: A => B): A => B = {
      a => f(a) <+> g(a)
    }
  }
}
