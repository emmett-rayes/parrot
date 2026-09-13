package parrot

/** A monoidal endoprofunctor over **Type**.
  *
  * Represents a profunctor *P*: **Type**^*op* × **Type** → **Type** equipped with a monoidal structure with respect to
  * the cartesian product × on **Type**, where
  *   - *unit*: *P*[Unit, Unit] is the unit element
  *   - ⊗: *P*[*A*,*B*] × *P*[*C*,*D*] → *P*[*A* × *C*, *B* × *D*] is the tensor product
  */
trait MonoidalProfunctor extends Profunctor {
  type Self[_, _]
  type P = Self

  /** The unit element of *P*[Unit, Unit].
    *
    * Unitality:
    *   - left identity: *P*(λ⁻¹, λ) ∘ (*unit* ⊗ *p*) = *p*
    *     - `unit.tensor(p).dimap(a => ((), a), (_, b) => b) == p`
    *   - right identity: *P*(ρ⁻¹, ρ) ∘ (*p* ⊗ *unit*) = *p*
    *     - `p.tensor(unit).dimap(a => (a, ()), (b, _) => b) == p`
    */
  def unit: P[Unit, Unit]

  extension [A, B](self: P[A, B])
    /** Combines two elements *p* in *P*[*A*,*B*] and *q* in *P*[*C*,*D*] to an element *p* ⊗ *q* in *P*[*A* × *C*, *B*
      * × *D*].
      *
      * Associativity:
      *   - *P*(α⁻¹, α) ∘ ((*p* ⊗ *q*) ⊗ *r*) = *p* ⊗ (*q* ⊗ *r*)
      *     - `self.tensor(other1).tensor(other2).dimap(((a, c), e) => (a, (c, e)), (b, (d, f)) => ((b, d), f)) == self.tensor(other1.tensor(other2))`
      */
    def tensor[C, D](other: P[C, D]): P[(A, C), (B, D)]

  extension [A, B](self: P[A, B])
    /** Alias for [[tensor]]. */
    def ***[C, D](other: P[C, D]): P[(A, C), (B, D)] = {
      self.tensor(other)
    }
}

object MonoidalProfunctor {

  /** Summons the `MonoidalProfunctor` instance of `P`. */
  def apply[P[_, _]: MonoidalProfunctor]: P is MonoidalProfunctor = {
    summon
  }
}
