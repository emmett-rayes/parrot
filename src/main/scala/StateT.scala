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
    def unit[A](a: A): S => M[(result: A, state: S)] = {
      s => M.unit((a, s))
    }

    extension [A](self: S => M[(result: S => M[(result: A, state: S)], state: S)])
      def flatten: S => M[(result: A, state: S)] = {
        s => self(s).flatMap((result, state) => result(state))
      }

    extension [A](self: S => M[(result: A, state: S)])
      def map[B](f: A => B): S => M[(result: B, state: S)] = {
        s => self(s).map((result, state) => (f(result), state))
      }
  }

  /** Every monoid *M* induces a monoid *T*, where
    *   - *T*[*A*] = *S* → *M*[*A* × *S*] are the elements
    *   - 0 = *s* ↦ 0' is the unit element
    *   - *t* + *u* = *s* ↦ *t*(*s*) +' *u*(*s*) is the monoid operation
    *
    * Here 0' and +' are the unit element and the monoid operation of *M*.
    */
  given StateTIsMonoidPlus: [S, M[_]: MonoidPlus] => (F: StateT[S, M] is Functor) => StateT[S, M] is MonoidPlus {
    export F.map

    def zero[A]: S => M[(result: A, state: S)] = {
      _ => M.zero
    }

    extension [A](self: S => M[(result: A, state: S)])
      def plus(other: S => M[(result: A, state: S)]): S => M[(result: A, state: S)] = {
        s => self(s).plus(other(s))
      }
  }

  /** Every restriction monad *M* with state *S* induces a restriction monad *T*, where
    *   - *T*[*A*] = *S* → *M*[*A* × *S*] are the elements
    *   - *t̄* = *s* ↦ *M*(_ ↦ ⟨(),*s*⟩)(*t*(*s*)̄') is the restriction operation
    *
    * Here *m̄'* is the restriction operation of *M*.
    */
  given StateTIsRestrictionMonad
    : [S, M[_]: RestrictionMonad] => (T: StateT[S, M] is Monad) => StateT[S, M] is RestrictionMonad {
    export T.{map, unit, flatten}

    extension [A](self: S => M[(result: A, state: S)])
      def restrict: StateT[S, M][Unit] = {
        state => self(state).restrict.map(_ => ((), state))
      }
  }
}
