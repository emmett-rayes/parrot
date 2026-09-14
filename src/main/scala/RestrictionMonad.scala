package parrot

/** A restriction monad over **Type**.
  *
  * Represents a monad *M* equipped with a restriction structure, where
  *   - _̄: *M*[*A*] → *M*[Unit] is the restriction operation
  */
trait RestrictionMonad extends Monad {
  type Self[_]
  type M = Self

  extension [A](self: M[A])
    /** Maps an element *m* in *M*[*A*] to its restriction idempotent *m̄* in *M*[Unit].
      *
      * Idempotence:
      *   - *m̄*̄ = *m̄*
      *     - `self.restrict.restrict == self.restrict`
      *
      * Unitality:
      *   - *η*(*a*)̄ = *η*(())
      *     - `unit(a).restrict == unit(())`
      *
      * Left Absorption:
      *   - *μ*(*M*(*_ ↦ m*)(*m̄*)) = *m*
      *     - `self.restrict.flatMap(_ => self) == self`
      *
      * Commutativity:
      *   - *μ*(*M*(*_ ↦ n̄*)(*m̄*)) = *μ*(*M*(*_ ↦ m̄*)(*n̄*))
      *     - `self.restrict.flatMap(_ => other.restrict) == other.restrict.flatMap(_ => self.restrict)`
      *
      * Here *η* and *μ* are the unit and the multiplication of *M*.
      */
    def restrict: M[Unit]
}

object RestrictionMonad {

  /** Summons the `RestrictionMonad` instance of `M`. */
  def apply[M[_]: RestrictionMonad]: M is RestrictionMonad = {
    summon
  }
}
