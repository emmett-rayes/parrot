package parrot

/** The Kleisli endoprofunctor of a monad *M* over **Type**.
  *
  * Represents a profunctor *K*: **Type**^*op* × **Type** → **Type**, where
  *   - *K*[*A*,*B*] = *A* → *M*[*B*] is the object part
  *   - *K*(*f*,*g*) = *f* ; - ; *M*(*g*) is the morphism part
  */
type Kleisli[M[_]] = [A, B] =>> A => M[B]

object Kleisli {

  /** Every functor *F* induces a profunctor *K*, where
    *   - *K*[*A*,*B*] = *A* → *F*[*B*] is the object part
    *   - *K*(*f*,*g*) = *f* ; - ; *F*(*g*) is the morphism part
    */
  given KleisliIsProfunctor: [F[_]: Functor] => Kleisli[F] is Profunctor {
    extension [A, B](self: Kleisli[F][A, B])
      def dimap[C, D](f: C => A, g: B => D): Kleisli[F][C, D] = {
        c => self(f(c)).map(g)
      }
  }

  /** Every monad *M* induces a promonad *K*, where
    *   - *K*[*A*,*B*] = *A* → *M*[*B*] are the elements
    *   - *η*(*f*) = *f* ; *η*' is the unit
    *   - *μ*(*p*,*q*) = *p* ; *M*(*q*) ; *μ*' is the multiplication
    *
    * Here *η*' and *μ*' are the unit and the multiplication of *M*.
    */
  given KleisliIsPromonad: [M[_]: Monad] => Kleisli[M] is Promonad {

    def unit[A, B](f: A => B): A => M[B] = {
      a => M.unit(f(a))
    }

    extension [A, B](self: A => M[B])
      def combine[C](other: B => M[C]): A => M[C] = {
        x => self(x).flatMap(other)
      }
  }
}
