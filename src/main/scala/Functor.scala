package parrot

/** An endofunctor over **Type**.
  *
  * Represents a functor *F*: **Type** → **Type**, where
  *   - *F*[*A*] is the object part
  *   - *F*(*f*) is the morphism part
  */
trait Functor {
  type Self[_]
  type F = Self

  extension [A](self: F[A])
    /** Maps a morphism *f*: *A* → *B* to a morphism *F*[*A*] → *F*[*B*].
      *
      * Functoriality:
      *   - identity: *F*(*id*) = *id*
      *     - `self.map(identity) == self`
      *   - composition: *F*(*g* ∘ *f*) = *F*(*g*) ∘ *F*(*f*)
      *     - `self.map(f).map(g) == self.map(f andThen g)`
      */
    def map[B](f: A => B): F[B]
}

object Functor {
  import scala.util.Try

  /** `Try` is a functor *F*, where
    *   - *F*[*A*] = *A* + *E* is the object part
    *   - *F*(*f*) = *f* + *id* is the morphism part
    *
    * Here *E* is the the type of failures, i.e. `Throwable`.
    */
  given TryIsFunctor: Try is Functor {
    extension [A](self: Try[A])
      def map[B](f: A => B): Try[B] = {
        self.map(f)
      }
  }
}
