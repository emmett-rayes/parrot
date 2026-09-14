package parrot

/** A comonoidal endoprofunctor over **Type**.
  *
  * Represents a profunctor *P*: **Type**^*op* × **Type** → **Type** equipped with a monoidal structure with respect to
  * the coproduct + on **Type**, where
  *   - *empty*: *P*[Nothing, Nothing] is the unit element
  *   - ⊕: *P*[*A*,*B*] × *P*[*C*,*D*] → *P*[*A* + *C*, *B* + *D*] is the sum
  */
trait CoMonoidalProfunctor extends Profunctor {
  type Self[_, _]
  type P = Self

  /** The unit element of *P*[Nothing, Nothing].
    *
    * Unitality:
    *   - left identity: *P*(λ⁻¹, λ) ∘ (*empty* ⊕ *p*) = *p*
    *     - `empty.sum(p).dimap(Right(_), _.merge) == p`
    *   - right identity: *P*(ρ⁻¹, ρ) ∘ (*p* ⊕ *empty*) = *p*
    *     - `p.sum(empty).dimap(Left(_), _.merge) == p`
    */
  def empty: P[Nothing, Nothing]

  extension [A, B](self: P[A, B])
    /** Combines two elements *p* in *P*[*A*,*B*] and *q* in *P*[*C*,*D*] to an element *p* ⊕ *q* in *P*[*A* + *C*, *B*
      * + *D*].
      *
      * Associativity:
      *   - *P*(α⁻¹, α) ∘ ((*p* ⊕ *q*) ⊕ *r*) = *p* ⊕ (*q* ⊕ *r*)
      */
    def sum[C, D](other: P[C, D]): P[Either[A, C], Either[B, D]]

  extension [A, B](self: P[A, B])
    /** Alias for [[sum]]. */
    def +++[C, D](other: P[C, D]): P[Either[A, C], Either[B, D]] = {
      self.sum(other)
    }
}

object CoMonoidalProfunctor {

  /** Summons the `CoMonoidalProfunctor` instance of `P`. */
  def apply[P[_, _]: CoMonoidalProfunctor]: P is CoMonoidalProfunctor = {
    summon
  }
}
