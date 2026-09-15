package parrot

/** A cartesian traced endopromonad over **Type**.
  *
  * Represents a promonad *P* equipped with a cartesian trace operator with respect to the cartesian product × on
  * **Type**, where
  *   - *trace*: *P*[*A* × *C*,*B* × *C*] → *P*[*A*,*B*] is the cartesian trace operation.
  *
  * @note A cartesian traced promonad is a special case of a cartesian costrong profunctor, with additional tightening
  *   and superposing laws.
  */
trait CartesianTracedPromonad extends Promonad {
  type Self[_, _]
  type P = Self

  extension [A, B, C](self: P[(A, C), (B, C)])
    /** Traces out the parameter *C*, yielding a morphism in *P*[*A*,*B*].
      *
      * Naturality:
      *   - `self.dimap(f *** identity, g *** identity).trace == self.trace.dimap(f, g)`
      *
      * Dinaturality (Sliding):
      *   - `self.lmap(identity *** h).trace == self.rmap(identity *** h).trace`
      *
      * Tightening:
      *   - `(unit(f *** identity) >>> self >>> unit(g *** identity)).trace == unit(f) >>> self.trace >>> unit(g)`
      *   - *((g ⊗ id) ∘ self ∘ (f ⊗ id))* traced = *g ∘ self.trace ∘ f*
      *
      * Unitality:
      *   - `self.dimap(in => (in, ()), out => out._1).trace == self`
      *
      * Associativity:
      *   - `self.dimap(in => ((in._1._1, in._1._2), in._2), out => ((out._1, out._2._1), out._2._2)).trace.trace == self.trace`
      *
      * Superposing:
      *   - Tracing preserves strength / tensoring with independent computations
      *
      * Here ∘ is the composition of the category induced by *P*.
      */
    def trace: P[A, B]
}

object CartesianTracedPromonad {

  /** Summons the `CartesianTracedPromonad` instance of `P`. */
  def apply[P[_, _]: CartesianTracedPromonad]: P is CartesianTracedPromonad = {
    summon
  }
}
