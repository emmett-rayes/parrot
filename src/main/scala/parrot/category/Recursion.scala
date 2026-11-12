package parrot
package category

/** A recursion structure on a promonad *P* over **C**.
  *
  * Represents fixed points at the types of the arrows of *P*, where
  *   - *fix*: (*P*(*A*,*B*) → *P*(*A*,*B*)) → *P*(*A*,*B*) is the fixed-point operator.
  *   - *fixFamily*: (*P*(*A*,*B*)ⁿ → *P*(*A*,*B*)ⁿ) → *P*(*A*,*B*)ⁿ is the fixed-point operator on a family of *n*
  *     arrows.
  *
  * It is a [[GuardedRecursion]] in which every function is guarded, and its laws are the laws of
  * [[GuardedRecursion]], without their premise.
  */
abstract class Recursion(tracked override val promonad: Promonad) extends GuardedRecursion(promonad)

object Recursion {

  /** The recursion structures on a promonad *P*. */
  type On[P <: Promonad] = Recursion { val promonad: P }
}
