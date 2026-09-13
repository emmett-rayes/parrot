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
}
