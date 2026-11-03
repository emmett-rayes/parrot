package parrot
package category

import Category.Type

/** A monad on a category **K**.
  *
  * Represents a monad (*M*, *η*, *μ*), where
  *   - *M* is an endofunctor on **K**, with action *M*(*f*) on morphisms
  *   - *η*: *A* → *M*[*A*], the unit
  *   - *μ*: *M*[*M*[*A*]] → *M*[*A*], the multiplication
  *
  * The unit and multiplication are the unit and multiplication of a monoid, with composition of endofunctors as the
  * tensor.
  */
abstract class Monad(tracked val functor: Endofunctor) extends caps.Pure {
  export functor.{F as M, category, map, objects}

  import category.{Obj, -->, >>>}

  private given MIsObj: [A: Obj] => (M[A] is Obj) = objects[A]

  /** The unit *η*: *A* → *M*[*A*]. */
  def unit[A: Obj]: A --> M[A]

  /** The multiplication *μ*: *M*[*M*[*A*]] → *M*[*A*]. */
  def flatten[A: Obj]: M[M[A]] --> M[A]

  /** The extension *f*\* = *μ* ∘ *M*(*f*): *M*[*A*] → *M*[*B*] of *f*: *A* → *M*[*B*]. */
  final def bind[A: Obj, B: Obj](f: A --> M[B]): M[A] --> M[B] = {
    map(f) >>> flatten[B]
  }

  /** Laws that any `Monad` must satisfy.
    *
    * A monad is a monoid with unit and multiplication as natural transformations.
    */
  object MonadLaws {

    /** *μ* ∘ *η*_*M* = *id*
      */
    def leftUnit[A: Obj](using (M[A] --> M[A]) is Observable): Boolean = {
      (unit[M[A]] >>> flatten[A]) =?= category.identity[M[A]]
    }

    /** *μ* ∘ *M*(*η*) = *id*
      */
    def rightUnit[A: Obj](using (M[A] --> M[A]) is Observable): Boolean = {
      (map(unit[A]) >>> flatten[A]) =?= category.identity[M[A]]
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

  /** The monads on a category **K**: refines the endofunctor, so that the category of a monad *M* is known as **K**. */
  type On[K <: Category] = Monad { val functor: Endofunctor.On[K] }

  /** The identity monad on 𝒮: computations without effects, where
    *   - *M*[*A*] = *A*
    *   - *η* = *id* and *μ* = *id*
    */
  object Identity extends Monad(Total.Identity) {

    def unit[A: Type]: A -> A = {
      a => a
    }

    def flatten[A: Type]: A -> A = {
      a => a
    }
  }

  /** `Option` is a monad on 𝒮, the failure transformer [[OptionT]] over the identity, where
    *   - *M*[*A*] = *A* + 1: a result or none
    *   - *η* = *Some*
    *   - *μ* keeps the inner result, or none
    */
  object OptionIsMonad extends OptionT(Identity)

  /** A restriction structure on a monad on 𝒮: a computation can be asked whether it succeeds, without its result.
    *
    * Represents a monad *M* with
    *   - *m̄*: *M*[*A*] → *M*[1], the computation that succeeds where *m* succeeds and has no other effect
    *
    * The laws are those of the Kleisli restriction structure it induces, [[Kleisli.RestrictionOf]].
    */
  abstract class Restriction(tracked val monad: On[Total.type]) extends caps.Pure {

    /** The restriction *m̄* of *m*. */
    def restrict[A](m: monad.M[A]): monad.M[Unit]
  }

  /** A classical restriction structure on a monad on 𝒮: success is decidable.
    *
    * Represents a monad *M* with
    *   - 0: *M*[*A*], the computation that fails
    *   - *m̄*ᶜ: *M*[1], which succeeds exactly where *m* fails
    *   - *m* ⊳ *n*, which runs *m* and, where *m* fails, *n*
    *   - *attempt*(*m*): *M*[1 + *A*], which never fails and says whether *m* did
    *
    * The laws are those of the Kleisli classical structure it induces, [[Kleisli.ClassicalOf]].
    */
  abstract class Classical(tracked override val monad: On[Total.type]) extends Restriction(monad) {

    /** The failing computation 0. */
    def zero[A]: monad.M[A]

    /** The complement *m̄*ᶜ: succeeds exactly where *m* fails. */
    def complement[A](m: monad.M[A]): monad.M[Unit]

    /** Override *m* ⊳ *n*: *m*, or *n* where *m* fails. *n* is passed by name, and computed only where *m* fails. */
    def orElse[A](m: monad.M[A], n: -> monad.M[A]): monad.M[A]

    /** *attempt*(*m*) = *M*(*Some*)(*m*) ⊳ *η*(*None*): the result of *m* if it succeeds.
      */
    def attempt[A](m: monad.M[A]): monad.M[Option[A]] = {
      orElse(monad.map[A, Option[A]](a => Some(a))(m), monad.unit[Option[A]](None))
    }
  }

  object Classical {

    /** `Option` is classical: `None` fails, and success can be tested. It is the classical structure of the failure
      * transformer over the identity.
      */
    object OptionIsClassical extends OptionT.ClassicalOf(OptionIsMonad)
  }

  /** An iteration operator on a monad on 𝒮.
    *
    * Represents a monad *M* with
    *   - *f*†: *X* → *M*[*A*] for *f*: *X* → *M*[*A* + *X*], which runs *f* until it returns an *A*
    *
    * In 𝒮 an iteration operator is guarded: it must stop on its own (see [[StateT.GuardedIteration]]). The laws are
    * those of the Kleisli iteration it induces, [[Kleisli.ElgotOf]].
    */
  abstract class Elgot(tracked val monad: On[Total.type]) extends caps.Pure {

    /** The iteration *f*† of *f*. */
    def iterate[A, X](f: X -> monad.M[Either[A, X]]): X -> monad.M[A]
  }
}
