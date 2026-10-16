package parrot
package category

import scala.annotation.targetName

/** A monad over **Type**.
  *
  * Represents a monoid in the monoidal category of endofunctors **End** over **Type**, where
  *   - *Id*, the identity functor, is the unit object of **End**
  *   - ∘ is the tensor product of **End**
  *   - *η*: *Id* ⇒ *M* is the unit of the monoid
  *   - *μ*: *M* ∘ *M* ⇒ *M* is the multiplication of the monoid, presented here via `flatten`
  */
trait Monad {
  type Self[_]: Functor as MonadFunctor
  final type M = Self

  val SelfIsFunctor: Self is Functor = MonadFunctor

  /** The unit natural transformation *η*: *Id* ⇒ *M*.
    *
    * Maps an element *a* in *A* to an element *η*(*a*) in *M*[*A*].
    */
  def unit[A](a: A): M[A]

  /** The multiplication natural transformation *μ*: *M* ∘ *M* ⇒ *M*.
    *
    * Maps an element *m* in *M*[*M*[*A*]] to an element *μ*(*m*) in *M*[*A*].
    */
  def flatten[A](m: M[M[A]]): M[A]

  extension [A](m: M[M[A]])
    /** Infix extension for [[flatten]]. */
    @targetName("flattenExt")
    def flatten(using DummyImplicit): M[A] = {
      Monad.this.flatten(m)
    }

  extension [A](m: M[A])
    /** Maps a morphism *f*: *A* ⇒ *M*[*B*] over an element *m* in *M*[*A*] and flattens the result (sequences *m* with
      * the continuation *f*).
      */
    def flatMap[B](f: A => M[B]): M[B] = {
      Monad.this.flatten(m.map(f))
    }

  /** Laws that any `Monad` must satisfy. */
  object MonadLaws {

    /** Left identity: *η*(*a*) >>= *f* = *f*(*a*) */
    def leftIdentity[A, B](a: A, f: A => M[B])(using M[B] is Eq): Boolean = {
      unit(a).flatMap(f) === f(a)
    }

    /** Right identity: *m* >>= *η* = *m* */
    def rightIdentity[A](m: M[A])(using M[A] is Eq): Boolean = {
      m.flatMap(unit) === m
    }

    /** Associativity: (*m* >>= *f*) >>= *g* = *m* >>= (*a* ↦ *f*(*a*) >>= *g*) */
    def associativity[A, B, C](m: M[A], f: A => M[B], g: B => M[C])(using M[C] is Eq): Boolean = {
      m.flatMap(f).flatMap(g) === m.flatMap(a => f(a).flatMap(g))
    }

    /** Unit naturality: *M*(*f*)(*η*(*a*)) = *η*(*f*(*a*)) */
    def unitNaturality[A, B](a: A, f: A => B)(using M[B] is Eq): Boolean = {
      unit(a).map(f) === unit(f(a))
    }

    /** Left unitality: *μ*(*η*(*m*)) = *m* */
    def leftUnitality[A](m: M[A])(using M[A] is Eq): Boolean = {
      unit(m).flatten === m
    }

    /** Right unitality: *μ*(*M*(*η*)(*m*)) = *m* */
    def rightUnitality[A](m: M[A])(using M[A] is Eq): Boolean = {
      m.map(unit).flatten === m
    }

    /** Multiplication naturality: *M*(*f*)(*μ*(*m*)) = *μ*(*M*(*M*(*f*))(*m*)) */
    def multiplicationNaturality[A, B](m: M[M[A]], f: A => B)(using M[B] is Eq): Boolean = {
      m.flatten.map(f) === m.map(_.map(f)).flatten
    }

    /** Multiplication associativity: *μ*(*μ*(*m*)) = *μ*(*M*(*μ*)(*m*)) */
    def multiplicationAssociativity[A](m: M[M[M[A]]])(using M[A] is Eq): Boolean = {
      m.flatten.flatten === m.map(_.flatten).flatten
    }
  }
}

object Monad {
  import scala.util.{Failure, Success, Try}

  /** Summons the `Monad` instance of `M`. */
  def apply[M[_]: Monad]: M is Monad = summon

  /** `Option` is a monad *M*, where
    *   - *M*[*A*] = *A* + 1 are the elements
    *   - *η*(*a*) = *ι*₁(*a*) is the unit (`Some(a)`)
    *   - *μ* = [*id*, *ι*₂] is the multiplication
    *
    * Here 1 is the unit type (`None`) and *ι*₁ and *ι*₂ are the injections into `Option`, i.e. `Some` and `None`.
    */
  given OptionIsMonad: Option is Monad {
    override given MonadFunctor: Functor.OptionIsFunctor.type = Functor.OptionIsFunctor
    override val SelfIsFunctor: Functor.OptionIsFunctor.type  = Functor.OptionIsFunctor

    def unit[A](a: A): Option[A] = {
      Some(a)
    }

    def flatten[A](m: Option[Option[A]]): Option[A] = m match {
      case Some(a) => a
      case None    => None
    }
  }

  /** `Try` is a monad *M*, where
    *   - *M*[*A*] = *A* + *E* are the elements
    *   - *η*(*a*) = *ι*₁(*a*) is the unit (`Success(a)`)
    *   - *μ* = [*id*, *ι*₂] is the multiplication
    *
    * Here *E* is the type of failures, i.e. `Throwable` and *ι*₁ and *ι*₂ are the injections into `Try`, i.e. `Success`
    * and `Failure`.
    */
  given TryIsMonad: Try is Monad {
    override given MonadFunctor: Functor.TryIsFunctor.type = Functor.TryIsFunctor
    override val SelfIsFunctor: Functor.TryIsFunctor.type  = Functor.TryIsFunctor

    def unit[A](a: A): Try[A] = {
      Success(a)
    }

    def flatten[A](m: Try[Try[A]]): Try[A] = m match {
      case Success(a) => a
      case Failure(e) => Failure(e)
    }
  }
}
