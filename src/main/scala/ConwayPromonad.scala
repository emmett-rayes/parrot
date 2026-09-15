package parrot

/** A Conway endopromonad over **Type**.
  *
  * Represents a promonad *P* equipped with a parameterized Conway fixed-point operator with respect to the cartesian
  * product × on **Type**, where
  *   - _^†: *P*[*A* × *C*,*C*] → *P*[*A*,*C*] is the parameterized Conway fixed-point operation.
  *
  * @note ConwayPromonads are in our cartesian setting equivalent to CartesianTracedPromonads.
  */
trait ConwayPromonad extends Promonad {
  type Self[_, _]
  type P = Self

  extension [A, C](self: P[(A, C), C])
    /** Maps an element *f* in *P*[*A* × *C*,*C*] to an element *f*^† in *P*[*A*,*C*].
      *
      * Fixed-point Property:
      *   - *f*^† = *f* ∘ ⟨*id*,*f*^†⟩
      *     - `unit((a: A) => (a, a)) >>> self.dagger.second >>> self == self.dagger`
      *
      * Parameter Naturality:
      *   - (*f* ∘ (*h* × *id*))^† = *f*^† ∘ *h*
      *     - `(unit((in: (A0, C)) => (h(in._1), in._2)) >>> self).dagger == unit(h) >>> self.dagger`
      *
      * Composition Identity (Dinaturality):
      *   - (*f* ∘ ⟨*g*,π₂⟩)^† = *f* ∘ ⟨(*g* ∘ ⟨*f*,π₂⟩)^†,*id*⟩
      *     - `(self >>> unit(g)).dagger == (unit((in: (A, D)) => (in._1, g(in._2))) >>> self).dagger >>> unit(g)`
      *
      * Double Dagger Identity (Diagonality / Bekić):
      *   - (*f* ∘ (*id* × Δ))^† = (*f*^†)^†
      *     - `(unit((in: (A, C)) => (in._1, (in._2, in._2))) >>> self).dagger == self.dagger.dagger`
      *
      * Here ∘ is the composition of the category induced by *P*, and
      *   - Δ: *C* → *C* × *C* is the diagonal morphism (duplicator) `c => (c, c)`
      *   - π₁: *A* × *B* → *A* and π₂: *A* × *B* → *B* are canonical projections `_._1` and `_._2`
      *   - ⟨*f*,*g*⟩: *A* → *B* × *C* is pairing `a => (f(a), g(a))`
      */
    def dagger: P[A, C]
}

object ConwayPromonad {

  /** Summons the `ConwayPromonad` instance of `P`. */
  def apply[P[_, _]: ConwayPromonad]: P is ConwayPromonad = {
    summon
  }

  /** Every Conway promonad induces a cartesian traced promonad, where trace is derived from the Conway dagger operator:
    * `trace(g) = π₁ ∘ (g ∘ (id × π₂))†`
    *
    * Here ∘ is the composition of the category induced by *P*.
    */
  given ConwayPromonadIsCartesianTracedPromonad: [P[_, _]] => (C: P is ConwayPromonad) => P is CartesianTracedPromonad {
    export C.unit
    export C.combine

    extension [A, B, C](self: P[(A, C), (B, C)])
      def trace: P[A, B] = {
        val step: P[(A, (B, C)), (B, C)] =
          C.unit((in: (A, (B, C))) => (in._1, in._2._2)).combine(self)
        step.dagger.combine(C.unit(_._1))
      }
  }
}
