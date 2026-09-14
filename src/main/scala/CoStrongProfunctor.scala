package parrot

/** A costrong endoprofunctor over **Type**.
  *
  * Represents a profunctor *P*: **Type**^*op* × **Type** → **Type** equipped with a cotensorial costrength with respect
  * to the coproduct + on **Type**, where
  *   - *left*: *P*[*A*,*B*] → *P*[*A* + *C*, *B* + *C*] is the left costrength
  *   - *right*: *P*[*C*,*D*] → *P*[*A* + *C*, *A* + *D*] is the right costrength
  */
trait CoStrongProfunctor extends Profunctor {
  type Self[_, _]
  type P = Self

  extension [A, B](self: P[A, B])
    /** Maps an element in *P*[*A*,*B*] to an element in *P*[*A* + *C*, *B* + *C*].
      *
      * Unitality:
      *   - identity: *P*(ρ⁻¹, ρ) ∘ *left* = *id*
      *     - `self.left[Nothing].dimap(Left(_), _.merge) == self`
      *
      * Associativity:
      *   - *P*(α⁻¹, α) ∘ *left* ∘ *left* = *left*
      *     - `self.left[C].left[D].dimap({ case Left(a) => Left(Left(a)); case Right(Left(c)) => Left(Right(c)); case Right(Right(d)) => Right(d) }, { case Left(Left(b)) => Left(b); case Left(Right(c)) => Right(Left(c)); case Right(d) => Right(Right(d)) }) == self.left[Either[C, D]]`
      */
    def left[C]: P[Either[A, C], Either[B, C]]

  extension [C, D](self: P[C, D])
    /** Maps an element in *P*[*C*,*D*] to an element in *P*[*A* + *C*, *A* + *D*]. */
    def right[A]: P[Either[A, C], Either[A, D]] = {
      self.left[A].dimap(_.swap, _.swap)
    }
}

object CoStrongProfunctor {

  /** Summons the `CoStrongProfunctor` instance of `P`. */
  def apply[P[_, _]: CoStrongProfunctor]: P is CoStrongProfunctor = {
    summon
  }
}
