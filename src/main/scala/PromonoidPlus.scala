package parrot

/** A **MonPlus**-valued profunctor.
  *
  * Represents a functor *P*: **Type**^*op* × **Type** → **MonPlus** into the "plus-flavoured" category of monoids,
  * where
  *   - 0: *P*[*A*,*B*] is the unit element
  *   - +: *P*[*A*,*B*] × *P*[*A*,*B*] → *P*[*A*,*B*] is the monoid operation
  *
  * Homomorphy:
  *   - zero: *P*(*f*,*g*)(0) = 0
  *     - `zero.dimap(f, g) == zero`
  *   - plus: *P*(*f*,*g*)(*x* + *y*) = *P*(*f*,*g*)(*x*) + *P*(*f*,*g*)(*y*)
  *     - `x.plus(y).dimap(f, g) == x.dimap(f, g).plus(y.dimap(f, g))`
  */
trait PromonoidPlus extends Profunctor {
  type Self[_, _]
  type P = Self

  /** The unit element 0 of *P*[*A*,*B*].
    *
    * Unitality:
    *   - left identity: 0 + *x* = *x*
    *     - `zero.plus(x) == x`
    *   - right identity: *x* + 0 = *x*
    *     - `x.plus(zero) == x`
    */
  def zero[A, B]: P[A, B]

  extension [A, B](self: P[A, B])
    /** Combines two elements *x*, *y* in *P*[*A*,*B*] to an element *x* + *y* in *P*[*A*,*B*].
      *
      * Associativity:
      *   - (*x* + *y*) + *z* = *x* + (*y* + *z*)
      *     - `self.plus(other1).plus(other2) == self.plus(other1.plus(other2))`
      */
    def plus(other: P[A, B]): P[A, B]

  extension [A, B](self: P[A, B])
    /** Alias for [[plus]]. */
    def <+>(other: P[A, B]): P[A, B] = {
      self.plus(other)
    }
}
