package parrot

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
  given StateTIsFunctor: [S, F[_]: Functor] => StateT[S, F] is Functor {
    extension [A](self: StateT[S, F][A])
      def map[B](f: A => B): StateT[S, F][B] = {
        s => self(s).map((result, state) => (f(result), state))
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
  given StateTIsMonad: [S, M[_]: Monad] => StateT[S, M] is Monad {
    def unit[A](a: A): StateT[S, M][A] = {
      s => M.unit((a, s))
    }

    extension [A](self: StateT[S, M][StateT[S, M][A]])
      def flatten: StateT[S, M][A] = {
        s => self(s).flatMap((result, state) => result(state))
      }

    extension [A](self: StateT[S, M][A])
      def map[B](f: A => B): StateT[S, M][B] = {
        s => self(s).map((result, state) => (f(result), state))
      }
  }
}
