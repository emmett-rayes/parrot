package parrot

/** The Kleisli endoprofunctor of a monad *M* over **Type**.
  *
  * Represents a profunctor *K*: **Type**^*op* × **Type** → **Type**, where
  *   - *K*[*A*,*B*] = *A* → *M*[*B*] is the object part
  *   - *K*(*f*,*g*) = *f* ; - ; *M*(*g*) is the morphism part
  */
type Kleisli[M[_]] = [A, B] =>> (M is Monad) ?=> A => M[B]
