package parrot

/** The state transformer of a monad *M* with state *S* over **Type**.
  *
  * Represents a functor *T*: **Type** → **Type**, where
  *   - *T*[*A*] = *S* → *M*[*A* × *S*] is the object part
  *   - *T*(*f*) = - ; *M*(*f* × *id*) is the morphism part
  */
type StateT[S, M[_]] = [A] =>> S => M[(result: A, state: S)]
