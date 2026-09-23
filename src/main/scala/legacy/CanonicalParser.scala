package parrot
package legacy

/** A canonical parser algebra interpreter whose operations are implemented via categorical typeclasses. */
trait CanonicalParser extends ParserAlgebra {
  type Self[_, _]: {Profunctor, Promonad, PromonoidPlus, RestrictionPromonad, CartesianMonoidalProfunctor,
    CocartesianMonoidalProfunctor, ElgotPromonad}

  def pure[A, B](f: A => B): P[A, B] = {
    Promonad[P].unit(f)
  }

  def failure[A, B]: P[A, B] = {
    PromonoidPlus[P].zero
  }

  extension [A, B](self: P[A, B])
    def lookahead: P[A, Unit] = {
      self.restrict.rmap(_ => ())
    }

  extension [A, B](self: P[A, B])
    def andThen[C](other: P[B, C]): P[A, C] = {
      self.combine(other)
    }

  extension [A, B](self: P[A, B])
    def orElse(other: P[A, B]): P[A, B] = {
      self.plus(other)
    }

  extension [A, B](self: P[A, B])
    def zip[C, D](other: P[C, D]): P[(A, C), (B, D)] = {
      self.tensor(other)
    }

  extension [A, B](self: P[A, B])
    def branch[C, D](other: P[C, D]): P[Either[A, C], Either[B, D]] = {
      self.sum(other)
    }

  extension [A, B](self: P[A, Either[B, A]])
    def loop: P[A, B] = {
      self.dagger
    }
}

object CanonicalParser {

  /** Summons the `CanonicalParser` instance of `P`. */
  def apply[P[_, _]: CanonicalParser]: P is CanonicalParser = {
    summon
  }
}
