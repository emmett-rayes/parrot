package parrot
package category

import scala.annotation.targetName

/** A restriction monad over **Type**.
  *
  * Represents a monad *M* equipped with a restriction structure, where
  *   - _̄: *M*[*A*] → *M*[Unit] is the restriction operation
  */
trait RestrictionMonad {
  type Self[_]: Monad as RestrictionMonadMonad
  final type M = Self

  val SelfIsMonad: Self is Monad = RestrictionMonadMonad

  /** Maps an element *m* in *M*[*A*] to its restriction idempotent *m̄* in *M*[Unit]. */
  def restrict[A](m: M[A]): M[Unit]

  extension [A](m: M[A])
    /** Infix extension for [[restrict]]. */
    @targetName("restrictExt")
    def restrict(using DummyImplicit): M[Unit] = {
      RestrictionMonad.this.restrict(m)
    }

  /** Laws that any `RestrictionMonad` must satisfy. */
  object RestrictionLaws {
    import SelfIsMonad.{flatMap, unit}

    /** Left Absorption: *m̄* >>= (_ ↦ *m*) = *m* */
    def absorption[A](m: M[A])(using M[A] is Eq): Boolean = {
      m.restrict.flatMap(_ => m) === m
    }

    /** Commutativity: *m̄* >>= (_ ↦ *n̄*) = *n̄* >>= (_ ↦ *m̄*) */
    def commutativity[A, B](m: M[A], n: M[B])(using M[Unit] is Eq): Boolean = {
      m.restrict.flatMap(_ => n.restrict) === n.restrict.flatMap(_ => m.restrict)
    }

    /** Unitality: *η*(*a*)̄ = *η*(()) */
    def unitality[A](a: A)(using M[Unit] is Eq): Boolean = {
      unit(a).restrict === unit(())
    }

    /** Idempotence: *m̄̄* = *m̄* */
    def idempotence[A](m: M[A])(using M[Unit] is Eq): Boolean = {
      m.restrict.restrict === m.restrict
    }
  }
}

object RestrictionMonad {
  import scala.util.Try

  /** Summons the `RestrictionMonad` instance of `M`. */
  def apply[M[_]: RestrictionMonad]: M is RestrictionMonad = summon

  /** `Option` is a restriction monad *M*, where
    *   - *M*[*A*] = *A* + 1 are the elements
    *   - *m̄* = *M*(_ ↦ ())(*m*) is the restriction operation
    *
    * Here 1 is the unit type (`None`).
    */
  given OptionIsRestrictionMonad: Option is RestrictionMonad {
    override given RestrictionMonadMonad: Monad.OptionIsMonad.type = Monad.OptionIsMonad
    override val SelfIsMonad: Monad.OptionIsMonad.type             = Monad.OptionIsMonad

    def restrict[A](m: Option[A]): Option[Unit] = {
      m.map(_ => ())
    }
  }

  /** `Try` is a restriction monad *M*, where
    *   - *M*[*A*] = *A* + *E* are the elements
    *   - *m̄* = *M*(_ ↦ ())(*m*) is the restriction operation
    *
    * Here *E* is the type of failures, i.e. `Throwable` shipping.
    */
  given TryIsRestrictionMonad: Try is RestrictionMonad {
    override given RestrictionMonadMonad: Monad.TryIsMonad.type = Monad.TryIsMonad
    override val SelfIsMonad: Monad.TryIsMonad.type             = Monad.TryIsMonad

    def restrict[A](m: Try[A]): Try[Unit] = {
      m.map(_ => ())
    }
  }
}
