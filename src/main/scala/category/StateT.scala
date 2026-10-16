package parrot
package category

import category.Valued.over

/** The state transformer of a monad *M* with state *S* over **Type**.
  *
  * Represents a functor *T*: **Type** → **Type**, where
  *   - *T*[*A*] = *S* → *M*[*A* × *S*] is the object part
  *   - *T*(*f*) = - ; *M*(*f* × *id*) is the morphism part
  */
type StateT[S, M[_]] = [A] =>> S => M[(result: A, state: S)]

object StateT {

  /** Every functor *F* induces a functor *T*, where
    *   - *T*[*A*] = *S* → *F*[*A* × *S*] is the object part
    *   - *T*(*f*) = - ; *F*(*f* × *id*) is the morphism part
    */
  given StateTIsFunctor: [S, K[_]] => (K: K is Functor) => StateT[S, K] is Functor = new Functor {
    type Self = StateT[S, K]

    import K.map

    def map[A, B](fa: StateT[S, K][A])(f: A => B): StateT[S, K][B] = {
      s => fa(s).map((result, state) => (result = f(result), state = state))
    }
  }

  /** Every monad *M* induces a monad *T*, where
    *   - *T*[*A*] = *S* → *M*[*A* × *S*] are the elements
    *   - *η*(*a*) = ⟨*a*,*id*⟩ ; *η*' is the unit
    *   - *μ*(*t*) = *t* ; *M*(*ev*) ; *μ*' is the multiplication
    *
    * Here *η*' and *μ*' are the unit and the multiplication of *M* and *ev*: *T*[*A*] × *S* → *M*[*A* × *S*] is the
    * underlying function.
    */
  given StateTIsMonad: [S, K[_]] => (K: K is Monad) => StateT[S, K] is Monad = {
    new Monad {
      type Self = StateT[S, K]

      override given MonadFunctor: StateT[S, K] is Functor = StateTIsFunctor[S, K](using K.SelfIsFunctor)

      import K.flatMap

      def unit[A](a: A): StateT[S, K][A] = {
        s => K.unit((result = a, state = s))
      }

      def flatten[A](m: StateT[S, K][StateT[S, K][A]]): StateT[S, K][A] = {
        s => m(s).flatMap((result, state) => result(state))
      }
    }
  }

  /** Every **V**-valued functor *F* with pointwise function types induces a **V**-valued state transformer *T*, where
    *   - *T*[*A*] = *S* → *F*[*A* × *S*] are in **V**
    */
  given StateTIsValued: [S, K[_], O <: Any { type Self }] => (
    K: K is (Valued over O),
    P: O is Pointwise,
  ) => StateT[S, K] is (Valued over O) = {
    new Valued {
      type Self = StateT[S, K]
      type Over = O

      override given ValuedFunctor: StateT[S, K] is Functor = StateTIsFunctor[S, K](using K.SelfIsFunctor)

      override given FIsV: [A] => (Self[A] is Over) = {
        P.FunctionIsV[S, K[(result: A, state: S)]](using K.FIsV[(result: A, state: S)])
      }
    }
  }

  /** Every restriction monad *M* with state *S* induces a restriction monad *T*, where
    *   - *T*[*A*] = *S* → *M*[*A* × *S*] are the elements
    *   - *t̄* = *s* ↦ *M*(_ ↦ ⟨(),*s*⟩)(*t*(*s*)̄') is the restriction operation
    *
    * Here *m̄'* is the restriction operation of *M*.
    */
  given StateTIsRestrictionMonad: [S, K[_]] => (K: K is RestrictionMonad) => StateT[S, K] is RestrictionMonad = {
    new RestrictionMonad {
      type Self = StateT[S, K]

      override given RestrictionMonadMonad: StateT[S, K] is Monad = StateTIsMonad[S, K](using K.SelfIsMonad)

      import K.SelfIsMonad.SelfIsFunctor.map
      import K.restrict

      def restrict[A](m: StateT[S, K][A]): StateT[S, K][Unit] = {
        state => m(state).restrict.map(_ => (result = (), state = state))
      }
    }
  }

  /** Every Elgot monad *M* with state *S* induces an Elgot monad *T*, where
    *   - *t*† = *s* ↦ *f*(*a*)(*s*)†' is the iteration operation
    *
    * Here *m*†' is the iteration operation of *M*.
    */
  given StateTIsElgotMonad: [S, K[_]] => (K: K is ElgotMonad) => StateT[S, K] is ElgotMonad = {
    new ElgotMonad {
      type Self = StateT[S, K]

      override given ElgotMonadMonad: StateT[S, K] is Monad = StateTIsMonad[S, K](using K.SelfIsMonad)

      import K.SelfIsMonad.SelfIsFunctor.map

      def iterate[A, B](f: A => StateT[S, K][Either[B, A]]): A => StateT[S, K][B] = {
        val step: ((result: A, state: S)) => K[Either[(result: B, state: S), (result: A, state: S)]] = {
          case (result, state) =>
            f(result)(state).map {
              case (Left(b), state2)  => Left((result = b, state = state2))
              case (Right(a), state2) => Right((result = a, state = state2))
            }
        }

        a => s => K.iterate(step)((result = a, state = s))
      }
    }
  }
}
