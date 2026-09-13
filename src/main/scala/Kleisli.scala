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
        a => self(a).flatMap(other)
      }
  }

  /** Every monoid *M* induces a promonoid *K*, where
    *   - *K*[*A*,*B*] = *A* → *M*[*B*] are the elements
    *   - 0 = *a* ↦ 0' is the unit element
    *   - *p* + *q* = *a* ↦ *p*(*a*) +' *q*(*a*) is the monoid operation
    *
    * Here 0' and +' are the unit element and the monoid operation of *M*.
    */
  given KleisliIsPromonoidPlus: [M[_]: MonoidPlus] => (P: Kleisli[M] is Profunctor) => Kleisli[M] is PromonoidPlus {
    export P.dimap

    def zero[A, B]: A => M[B] = {
      _ => M.zero
    }

    extension [A, B](self: A => M[B])
      def plus(other: A => M[B]): A => M[B] = {
        a => self(a).plus(other(a))
      }
  }

  /** Every monad *M* induces a strong profunctor *K*, where
    *   - *K*[*A*,*B*] = *A* → *M*[*B*] are the elements
    *   - *first*(*k*) = (*a*,*c*) ↦ *M*(⟨*id*,*c*⟩)(*k*(*a*)) is the strength
    */
  given KleisliIsStrongProfunctor: [M[_]: Monad] => (P: Kleisli[M] is Profunctor) => Kleisli[M] is StrongProfunctor {
    export P.dimap

    extension [A, B](self: A => M[B])
      def first[C]: ((A, C)) => M[(B, C)] = {
        (a, c) => self(a).map((_, c))
      }
  }
}
