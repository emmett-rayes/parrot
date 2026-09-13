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
