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
}
