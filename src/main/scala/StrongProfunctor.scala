package parrot

/** A strong endoprofunctor over **Type**.
  *
  * Represents a profunctor *P*: **Type**^*op* × **Type** → **Type** equipped with a tensorial strength with respect to
  * the cartesian product × on **Type**, where
  *   - *first*: *P*[*A*,*B*] → *P*[*A* × *C*, *B* × *C*] is the left strength
  *   - *second*: *P*[*C*,*D*] → *P*[*A* × *C*, *A* × *D*] is the right strength
  */
trait StrongProfunctor extends Profunctor {
  type Self[_, _]
  type P = Self

  extension [A, B](self: P[A, B])
    /** Maps an element in *P*[*A*,*B*] to an element in *P*[*A* × *C*, *B* × *C*].
      *
      * Unitality:
      *   - identity: *P*(ρ⁻¹, ρ) ∘ *first* = *id*
      *     - `self.first[Unit].dimap(a => (a, ()), (b, _) => b) == self`
      *
      * Associativity:
      *   - *P*(α⁻¹, α) ∘ *first* ∘ *first* = *first*
      *     - `self.first[C].first[D].dimap((a, (c, d)) => ((a, c), d), ((b, c), d) => (b, (c, d))) == self.first[(C, D)]`
      */
    def first[C]: P[(A, C), (B, C)]

  extension [C, D](self: P[C, D])
    /** Maps an element in *P*[*C*,*D*] to an element in *P*[*A* × *C*, *A* × *D*]. */
    def second[A]: P[(A, C), (A, D)] = {
      self.first[A].dimap(_.swap, _.swap)
    }
}

object StrongProfunctor {

  /** Summons the `StrongProfunctor` instance of `P`. */
  def apply[P[_, _]: StrongProfunctor]: P is StrongProfunctor = {
    summon
  }
}
