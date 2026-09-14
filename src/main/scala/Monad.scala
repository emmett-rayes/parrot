package parrot

/** A monad over **Type**.
  *
  * Represents a monoid in the monoidal category of endofunctors **End** over **Type**, where
  *   - *Id*, the identity functor, is the unit object of **End**
  *   - ∘ is the tensor product of **End**
  *   - *η*: *Id* ⇒ *M* is the unit of the monoid
  *   - *μ*: *M* ∘ *M* ⇒ *M* is the multiplication of the monoid
  */
trait Monad extends Functor {
  type Self[_]
  type M = Self

  /** The unit natural transformation *η*: *Id* ⇒ *M*.
    *
    * Maps an element *a* in *A* to an element *η*(*a*) in *M*[*A*].
    *
    * Naturality:
    *   - *M*(*f*)(*η*(*a*)) = *η*(*f*(*a*))
    *     - `unit(a).map(f) == unit(f(a))`
    *
    * Unitality:
    *   - left identity: *μ*(*η*(*m*)) = *m*
    *     - `unit(m).flatten == m`
    *   - right identity: *μ*(*M*(*η*)(*m*)) = *m*
    *     - `m.map(unit).flatten == m`
    */
  def unit[A](a: A): M[A]

  extension [A](self: M[M[A]])
    /** The multiplication natural transformation *μ*: *M* ∘ *M* ⇒ *M*.
      *
      * Maps an element *m* in *M*[*M*[*A*]] to an element *μ*(*m*) in *M*[*A*].
      *
      * Naturality:
      *   - *M*(*f*)(*μ*(*m*)) = *μ*(*M*(*M*(*f*))(*m*))
      *     - `self.flatten.map(f) == self.map(_.map(f)).flatten`
      *
      * Associativity:
      *   - *μ*(*μ*(*m*)) = *μ*(*M*(*μ*)(*m*))
      *     - `self.flatten.flatten == self.map(_.flatten).flatten`
      */
    def flatten: M[A]

  extension [A](self: M[A])
    /** Maps a morphism *f*: *A* → *M*[*B*] over an element *m* in *M*[*A*] and flattens the result. */
    def flatMap[B](f: A => M[B]): M[B] = {
      self.map(f).flatten
    }
}

object Monad {
  import scala.util.Try

  /** Summons the `Monad` instance of `M`. */
  def apply[M[_]: Monad]: M is Monad = {
    summon
  }

  /** `Try` is a monad *M*, where
    *   - *M*[*A*] = *A* + *E* are the elements
    *   - *η*(*a*) = *ι*₁(*a*) is the unit
    *   - *μ* = [*id*,*ι*₂] is the multiplication
    *
    * Here *E* is the type of failures, i.e. `Throwable` and *ι*₁ and *ι*₂ are the injections into `Try`, i.e. `Success`
    * and `Failure`.
    */
  given TryIsMonad: (F: Try is Functor) => Try is Monad {
    export F.map

    def unit[A](a: A): Try[A] = {
      scala.util.Success(a)
    }

    extension [A](self: Try[Try[A]])
      def flatten: Try[A] = {
        self.flatten
      }
  }
}
