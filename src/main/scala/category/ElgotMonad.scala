package parrot
package category

/** An Elgot monad over **Type**.
  *
  * Represents a monad *M* equipped with an iteration operator with respect to the coproduct + on **Type**, where
  *   - _†: (*A* → *M*[*B* + *A*]) → (*A* → *M*[*B*]) is the Elgot iteration operation.
  */
trait ElgotMonad {
  type Self[_]: Monad as ElgotMonadMonad
  final type M = Self

  val SelfIsMonad: Self is Monad = ElgotMonadMonad

  /** Maps a step morphism *f*: *A* → *M*[*B* + *A*] and an initial state *a* in *A* to an iterated computation in
    * *M*[*B*].
    */
  def iterate[A, B](f: A => M[Either[B, A]]): A => M[B]

  /** Laws that any `ElgotMonad` must satisfy. */
  object ElgotLaws {
    import SelfIsMonad.{flatMap, unit}

    /** *f*†(*a*) = *f*(*a*) >>= [*η*, *f*†]
      */
    def fixedPoint[A, B](f: A => M[Either[B, A]], a: A)(using M[B] is Eq): Boolean = {
      iterate(f)(a) === f(a).flatMap(_.fold(unit, iterate(f)))
    }
  }
}

object ElgotMonad {
  import scala.util.{Failure, Success, Try}

  /** Summons the `ElgotMonad` instance of `M`. */
  def apply[M[_]: ElgotMonad]: M is ElgotMonad = summon

  /** `Option` is an Elgot monad *M* with iteration computing a tail-recursive loop. */
  given OptionIsElgotMonad: Option is ElgotMonad {
    override given ElgotMonadMonad: Monad.OptionIsMonad.type = Monad.OptionIsMonad
    override val SelfIsMonad: Monad.OptionIsMonad.type       = Monad.OptionIsMonad

    def iterate[A, B](f: A => Option[Either[B, A]]): A => Option[B] = {
      @annotation.tailrec
      def loop(a: A): Option[B] = f(a) match {
        case Some(Left(b))  => Some(b)
        case Some(Right(a)) => loop(a)
        case None           => None
      }
      loop
    }
  }

  /** `Try` is an Elgot monad *M* with iteration computing a tail-recursive loop. */
  given TryIsElgotMonad: Try is ElgotMonad {
    override given ElgotMonadMonad: Monad.TryIsMonad.type = Monad.TryIsMonad
    override val SelfIsMonad: Monad.TryIsMonad.type       = Monad.TryIsMonad

    def iterate[A, B](f: A => Try[Either[B, A]]): A => Try[B] = {
      @annotation.tailrec
      def loop(a: A): Try[B] = f(a) match {
        case Success(Left(b))  => Success(b)
        case Success(Right(a)) => loop(a)
        case Failure(e)        => Failure(e)
      }
      loop
    }
  }
}
