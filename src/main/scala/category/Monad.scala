package parrot
package category

/** A monad over **Type**.
  *
  * Represents a monoid in the monoidal category of endofunctors on **Type**, where
  *   - *η*: *Id* ⇒ *M* is the unit
  *   - *μ*: *M* ∘ *M* ⇒ *M* is the multiplication, presented here via `flatMap`
  */
trait Monad {
  type Self[_]
  final type M = Self

  /** The unit *η*: *A* → *M*[*A*]. */
  def unit[A](a: A): M[A]

  extension [A](m: M[A])
    /** Sequences *m* with the continuation *f*. */
    def flatMap[B](f: A => M[B]): M[B]

    /** The functorial action *M*(*f*). */
    def map[B](f: A => B): M[B] = m.flatMap(a => unit(f(a)))

  /** Laws that any `Monad` must satisfy. */
  object MonadLaws {

    /** *η*(*a*) >>= *f* = *f*(*a*) */
    def leftIdentity[A, B](a: A, f: A => M[B])(using M[B] is Eq): Boolean = {
      unit(a).flatMap(f) === f(a)
    }

    /** *m* >>= *η* = *m* */
    def rightIdentity[A](m: M[A])(using M[A] is Eq): Boolean = {
      m.flatMap(unit) === m
    }

    /** (*m* >>= *f*) >>= *g* = *m* >>= (*a* ↦ *f*(*a*) >>= *g*) */
    def associativity[A, B, C](m: M[A], f: A => M[B], g: B => M[C])(using M[C] is Eq): Boolean = {
      m.flatMap(f).flatMap(g) === m.flatMap(a => f(a).flatMap(g))
    }
  }
}

object Monad {

  /** Summons the `Monad` instance of `M`. */
  def apply[M[_]: Monad]: M is Monad = summon

  /** A monad whose elements form a monoid (0, +) for every *A*, with 0 a left zero of `flatMap`. */
  trait Plus extends Monad {
    type Self[_]

    /** The unit element 0 of *M*[*A*]. */
    def zero[A]: M[A]

    extension [A](m: M[A])
      /** The monoid operation *m* + *n* on *M*[*A*]. */
      def plus(n: M[A]): M[A]

    /** Laws that any `Monad.Plus` must satisfy. */
    object PlusLaws {

      /** 0 + *m* = *m* */
      def leftIdentity[A](m: M[A])(using M[A] is Eq): Boolean = zero[A].plus(m) === m

      /** *m* + 0 = *m* */
      def rightIdentity[A](m: M[A])(using M[A] is Eq): Boolean = m.plus(zero[A]) === m

      /** (*m* + *n*) + *o* = *m* + (*n* + *o*) */
      def associativity[A](m: M[A], n: M[A], o: M[A])(using M[A] is Eq): Boolean = {
        m.plus(n).plus(o) === m.plus(n.plus(o))
      }

      /** 0 >>= *f* = 0 */
      def leftZero[A, B](f: A => M[B])(using M[B] is Eq): Boolean = zero[A].flatMap(f) === zero[B]
    }
  }

  /** A monad equipped with a restriction *m̄*: *M*[*A*] → *M*[Unit], keeping the definedness of *m* but none of its
    * effects beyond it.
    */
  trait Restriction extends Monad {
    type Self[_]

    extension [A](m: M[A])
      /** The restriction idempotent *m̄* of *m*. */
      def restrict: M[Unit]

    /** Laws that any `Monad.Restriction` must satisfy. */
    object RestrictionLaws {

      /** *m̄* >>= (_ ↦ *m*) = *m* */
      def absorption[A](m: M[A])(using M[A] is Eq): Boolean = m.restrict.flatMap(_ => m) === m

      /** *m̄* >>= (_ ↦ *n̄*) = *n̄* >>= (_ ↦ *m̄*) */
      def commutativity[A, B](m: M[A], n: M[B])(using M[Unit] is Eq): Boolean = {
        m.restrict.flatMap(_ => n.restrict) === n.restrict.flatMap(_ => m.restrict)
      }

      /** η(*a*)‾ = η(()) */
      def unitality[A](a: A)(using M[Unit] is Eq): Boolean = unit(a).restrict === unit(())
    }
  }

  /** A monad equipped with an Elgot iteration *f*†: *A* → *M*[*B*] of a step *f*: *A* → *M*[*B* + *A*]. */
  trait Elgot extends Monad {
    type Self[_]

    /** Iterates *f* from *a* while it yields on the right. */
    def iterate[A, B](f: A => M[Either[B, A]]): A => M[B]

    /** Laws that any `Monad.Elgot` must satisfy. */
    object ElgotLaws {

      /** *f*†(*a*) = *f*(*a*) >>= [*η*, *f*†] */
      def fixedPoint[A, B](f: A => M[Either[B, A]], a: A)(using M[B] is Eq): Boolean = {
        iterate(f)(a) === f(a).flatMap(_.fold(unit, iterate(f)))
      }
    }
  }

  /** `Option` is a monad with ordered choice, restriction and iteration. */
  given OptionIsMonad: Option is (Plus & Restriction & Elgot) = new Plus with Restriction with Elgot {
    type Self[A] = Option[A]

    def unit[A](a: A): Option[A] = Some(a)

    extension [A](m: Option[A])
      def flatMap[B](f: A => Option[B]): Option[B] = m match {
        case Some(a) => f(a)
        case None    => None
      }

      def plus(n: Option[A]): Option[A] = m.orElse(n)

      def restrict: Option[Unit] = m.map(_ => ())

    def zero[A]: Option[A] = None

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
}
