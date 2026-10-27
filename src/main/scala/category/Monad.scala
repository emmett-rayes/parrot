package parrot
package category

/** A monad on a category **K**: structure on an endofunctor *M*, a monoid in the endofunctors on **K**.
  *
  * Represents a monad (*M*, *η*, *μ*), where
  *   - *M* = `M` is the endofunctor [[F]], with action *M*(*f*) = `map`
  *   - *η*: *A* → *M*[*A*], the unit, returns a value without effect
  *   - *μ*: *M*[*M*[*A*]] → *M*[*A*], the multiplication `flatten`, merges two layers of effects into one
  *
  * The extension *f*\* = *μ* ∘ *M*(*f*): *M*[*A*] → *M*[*B*] of *f*: *A* → *M*[*B*] is derived (`bind`); its arrows *A*
  * → *M*[*B*] form the [[Kleisli]] promonad. The unit and multiplication are the unit and multiplication of a monoid
  * (compare [[Monoid]]), with composition of endofunctors as the tensor.
  */
abstract class Monad(tracked val F: Endofunctor) extends caps.Pure {

  /** From the endofunctor: the category **K** the monad is on, the object part *M* = `M`, its action *M*(*f*) =
    * `map(f)` on morphisms, and `objects`, which says that *M* maps objects to objects.
    */
  export F.{F as M, K, map, objects}

  import K.{Obj, -->, >>>}

  private given MIsObj: [A: Obj] => (M[A] is Obj) = objects[A]

  /** The unit *η*: *A* → *M*[*A*]. */
  def unit[A: Obj]: A --> M[A]

  /** The multiplication *μ*: *M*[*M*[*A*]] → *M*[*A*]. */
  def flatten[A: Obj]: M[M[A]] --> M[A]

  /** The extension *f*\* = *μ* ∘ *M*(*f*): *M*[*A*] → *M*[*B*] of *f*: *A* → *M*[*B*]. */
  final def bind[A: Obj, B: Obj](f: A --> M[B]): M[A] --> M[B] = {
    map(f) >>> flatten[B]
  }

  /** Laws that any `Monad` must satisfy beyond the [[Functor.FunctorLaws]] of *M*: those of a monoid, and the
    * naturality of *η* and *μ*.
    */
  object MonadLaws {

    /** *μ* ∘ *η*_*M* = *id*
      */
    def leftUnit[A: Obj](using (M[A] --> M[A]) is Observable): Boolean = {
      (unit[M[A]] >>> flatten[A]) =?= K.identity[M[A]]
    }

    /** *μ* ∘ *M*(*η*) = *id*
      */
    def rightUnit[A: Obj](using (M[A] --> M[A]) is Observable): Boolean = {
      (map(unit[A]) >>> flatten[A]) =?= K.identity[M[A]]
    }

    /** *μ* ∘ *μ*_*M* = *μ* ∘ *M*(*μ*)
      */
    def associativity[A: Obj](using (M[M[M[A]]] --> M[A]) is Observable): Boolean = {
      (flatten[M[A]] >>> flatten[A]) =?= (map(flatten[A]) >>> flatten[A])
    }

    /** *M*(*f*) ∘ *η* = *η* ∘ *f*
      */
    def unitNaturality[A: Obj, B: Obj](f: A --> B)(using (A --> M[B]) is Observable): Boolean = {
      (unit[A] >>> map(f)) =?= (f >>> unit[B])
    }

    /** *M*(*f*) ∘ *μ* = *μ* ∘ *M*(*M*(*f*))
      */
    def flattenNaturality[A: Obj, B: Obj](f: A --> B)(using (M[M[A]] --> M[B]) is Observable): Boolean = {
      (flatten[A] >>> map(f)) =?= (map(map(f)) >>> flatten[B])
    }
  }
}

object Monad {

  /** The monads on **C**: refines the endofunctor, so that the category of a monad *M* is known as `M.K`. */
  type On[C <: Category] = Monad { val F: Endofunctor { val K: C } }

  /** `Option` is a monad on 𝒮, where
    *   - *M*[*A*] = *A* + 1: a result or none
    *   - *η* = `Some`
    *   - *μ* keeps the inner result, or none
    */
  object OptionIsMonad extends Monad(Endofunctor.OptionIsEndofunctor) {

    def unit[A: Type]: A -> Option[A] = {
      a => Some(a)
    }

    def flatten[A: Type]: Option[Option[A]] -> Option[A] = {
      _.flatten
    }
  }
}
