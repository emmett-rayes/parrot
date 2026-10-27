package parrot
package category

/** A restriction structure on a monad on 𝒮: a computation can be asked whether it succeeds, without its result.
  *
  * Represents a monad *M* with
  *   - *m̄*: *M*[*A*] → *M*[1], the computation that succeeds where *m* succeeds and has no other effect
  *
  * The laws are those of the Kleisli restriction structure it induces, [[Kleisli.RestrictionOf]].
  */
abstract class RestrictionMonad(tracked val M: Monad.On[Total.type]) extends caps.Pure {

  /** The restriction *m̄* of *m*. */
  def restrict[A](m: M.M[A]): M.M[Unit]
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
abstract class ClassicalMonad(tracked override val M: Monad.On[Total.type]) extends RestrictionMonad(M) {

  /** The failing computation 0. */
  def zero[A]: M.M[A]

  /** The complement *m̄*ᶜ: succeeds exactly where *m* fails. */
  def complement[A](m: M.M[A]): M.M[Unit]

  /** Override *m* ⊳ *n*: *m*, or *n* where *m* fails. `n` is passed by name, and computed only where *m* fails. */
  def orElse[A](m: M.M[A], n: -> M.M[A]): M.M[A]

  /** *attempt*(*m*) = *M*(`Some`)(*m*) ⊳ *η*(`None`): the result of *m* if it succeeds.
    */
  def attempt[A](m: M.M[A]): M.M[Option[A]] = {
    orElse(M.map[A, Option[A]](a => Some(a))(m), M.unit[Option[A]](None))
  }
}

object ClassicalMonad {

  /** `Option` is classical: `None` fails, and success can be tested. */
  object OptionIsClassical extends ClassicalMonad(Monad.OptionIsMonad) {

    def restrict[A](m: Option[A]): Option[Unit] = {
      m.map(_ => ())
    }

    def zero[A]: Option[A] = {
      None
    }

    def complement[A](m: Option[A]): Option[Unit] = {
      if m.isEmpty then Some(()) else None
    }

    def orElse[A](m: Option[A], n: -> Option[A]): Option[A] = {
      m.orElse(n)
    }

    override def attempt[A](m: Option[A]): Option[Option[A]] = {
      Some(m)
    }
  }
}

/** An iteration operator on a monad on 𝒮.
  *
  * Represents a monad *M* with
  *   - *f*†: *X* → *M*[*A*] for *f*: *X* → *M*[*A* + *X*], which runs *f* until it returns an *A*
  *
  * In 𝒮 an iteration operator is guarded: it must stop on its own (see [[StateT.GuardedIteration]]). The laws are
  * those of the Kleisli iteration it induces, [[Kleisli.ElgotOf]].
  */
abstract class ElgotMonad(tracked val M: Monad.On[Total.type]) extends caps.Pure {

  /** The iteration *f*† of *f*. */
  def iterate[A, X](f: X -> M.M[Either[A, X]]): X -> M.M[A]
}
