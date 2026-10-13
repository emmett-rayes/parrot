package parrot
package category

import scala.annotation.targetName

/** An endofunctor over **Type**.
  *
  * Represents a functor *F*: **Type** ⇒ **Type**, where
  *   - *F*[*A*] is the object part
  *   - *F*(*f*) is the morphism part
  */
trait Functor {
  type Self[_]
  final type F = Self

  /** Maps a morphism *f*: *A* ⇒ *B* to a morphism *F*[*A*] ⇒ *F*[*B*]. */
  def map[A, B](fa: F[A])(f: A => B): F[B]

  extension [A](fa: F[A])
    /** Infix extension for [[map]]. */
    @targetName("mapExt")
    def map[B](f: A => B): F[B] = {
      Functor.this.map(fa)(f)
    }

  /** Laws that any `Functor` must satisfy. */
  object FunctorLaws {

    /** *F*(*id*) = *id*
      */
    def identity[A](fa: F[A])(using F[A] is Eq): Boolean = {
      fa.map(scala.Predef.identity) === fa
    }

    /** *F*(*g* ∘ *f*) = *F*(*g*) ∘ *F*(*f*)
      */
    def composition[A, B, C](fa: F[A], f: A => B, g: B => C)(using F[C] is Eq): Boolean = {
      fa.map(f).map(g) === fa.map(f andThen g)
    }
  }
}

object Functor {
  import scala.util.Try

  /** Summons the `Functor` instance of `F`. */
  def apply[F[_]: Functor]: F is Functor = summon

  /** `Option` is a functor *F* on **Type**, where
    *   - *F*[*A*] = *A* + 1 is the object part
    *   - *F*(*f*) = *f* + *id* is the morphism part
    */
  given OptionIsFunctor: Option is Functor {
    def map[A, B](fa: Option[A])(f: A => B): Option[B] = {
      fa.map(f)
    }
  }

  /** `Try` is a functor *F*, where
    *   - *F*[*A*] = *A* + *E* is the object part
    *   - *F*(*f*) = *f* + *id* is the morphism part
    *
    * Here *E* is the type of failures, i.e. `Throwable`.
    */
  given TryIsFunctor: Try is Functor {
    def map[A, B](fa: Try[A])(f: A => B): Try[B] = {
      fa.map(f)
    }
  }
}
