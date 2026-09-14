package parrot

/** A cocartesian monoidal endoprofunctor over **Type**.
  *
  * Represents a profunctor *P*: **Type**^*op* × **Type** → **Type** equipped with a monoidal structure with respect to
  * the coproduct + on **Type**, where
  *   - *empty*: *P*[Nothing, Nothing] is the unit element
  *   - ⊕: *P*[*A*,*B*] × *P*[*C*,*D*] → *P*[*A* + *C*, *B* + *D*] is the sum
  */
trait CocartesianMonoidalProfunctor extends Profunctor {
  type Self[_, _]
  type P = Self

  /** The unit element of *P*[Nothing, Nothing].
    *
    * Unitality:
    *   - left identity: *P*(λ⁻¹, λ) ∘ (*empty* ⊕ *p*) = *p*
    *     - `(empty +++ p).dimap(Right(_), _.merge) == p`
    *   - right identity: *P*(ρ⁻¹, ρ) ∘ (*p* ⊕ *empty*) = *p*
    *     - `(p +++ empty).dimap(Left(_), _.merge) == p`
    */
  def empty: P[Nothing, Nothing]

  extension [A, B](self: P[A, B])
    /** Combines two elements *p* in *P*[*A*,*B*] and *q* in *P*[*C*,*D*] to an element *p* ⊕ *q* in *P*[*A* + *C*, *B*
      * + *D*].
      *
      * Associativity:
      *   - *P*(α⁻¹, α) ∘ ((*p* ⊕ *q*) ⊕ *r*) = *p* ⊕ (*q* ⊕ *r*)
      *     - `((self +++ other1) +++ other2).dimap({ case Left(Left(a)) => Left(a); case Left(Right(c)) => Right(Left(c)); case Right(e) => Right(Right(e)) }, { case Left(b) => Left(Left(b)); case Right(Left(d)) => Left(Right(d)); case Right(Right(f)) => Right(f) }) == self +++ (other1 +++ other2)`
      */
    def sum[C, D](other: P[C, D]): P[Either[A, C], Either[B, D]]

  extension [A, B](self: P[A, B])
    /** Alias for [[sum]]. */
    def +++[C, D](other: P[C, D]): P[Either[A, C], Either[B, D]] = {
      self.sum(other)
    }
}

object CocartesianMonoidalProfunctor {

  /** Summons the `CocartesianMonoidalProfunctor` instance of `P`. */
  def apply[P[_, _]: CocartesianMonoidalProfunctor]: P is CocartesianMonoidalProfunctor = {
    summon
  }
}
