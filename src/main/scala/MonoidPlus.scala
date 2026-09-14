package parrot

/** A **MonPlus**-valued functor.
  *
  * Represents a functor *F*: **Type** → **MonPlus** into the "plus-flavoured" category of monoids, where
  *   - 0: *F*[*A*] is the unit element
  *   - +: *F*[*A*] × *F*[*A*] → *F*[*A*] is the monoid operation
  */
trait MonoidPlus extends Functor {
  type Self[_]
  type M = Self

  /** The unit element 0 of *M*[*A*].
    *
    * Unitality:
    *   - left identity: 0 + *x* = *x*
    *     - `zero.plus(x) == x`
    *   - right identity: *x* + 0 = *x*
    *     - `x.plus(zero) == x`
    */
  def zero[A]: M[A]

  extension [A](self: M[A])
    /** Combines two elements *x*, *y* in *M*[*A*] to an element *x* + *y* in *M*[*A*].
      *
      * Associativity:
      *   - (*x* + *y*) + *z* = *x* + (*y* + *z*)
      *     - `self.plus(other1).plus(other2) == self.plus(other1.plus(other2))`
      */
    def plus(other: M[A]): M[A]

  extension [A](self: M[A])
    /** Alias for [[plus]]. */
    def +(other: M[A]): M[A] = {
      self.plus(other)
    }
}

object MonoidPlus {
  import scala.util.Try

  /** Summons the `MonoidPlus` instance of `M`. */
  def apply[M[_]: MonoidPlus]: M is MonoidPlus = {
    summon
  }

  /** `Try` is a monoid *M*, where
    *   - *M*[*A*] = *A* + *E* are the elements
    *   - 0 = *ι*₂(*e*) is the unit element, for an arbitrary failure *e*
    *   - *ι*₁(*a*) + *y* = *ι*₁(*a*) and *ι*₂(*e*) + *y* = *y* is the monoid operation
    *
    * Here *E* is the type of failures, i.e. `Throwable`, and *ι*₁ and *ι*₂ are the injections into `Try`, i.e.
    * `Success` and `Failure`.
    */
  given TryIsMonoidPlus: (F: Try is Functor) => Try is MonoidPlus {
    import scala.util.Failure

    export F.map

    def zero[A]: Try[A] = {
      Failure[A](Exception())
    }

    extension [A](self: Try[A])
      override def plus(other: Try[A]): Try[A] = {
        self.orElse(other)
      }
  }
}
