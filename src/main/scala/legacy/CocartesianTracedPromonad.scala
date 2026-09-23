package parrot
package legacy

/** A cocartesian traced endopromonad over **Type**.
  *
  * Represents a promonad *P* equipped with a cocartesian trace operator with respect to the coproduct + on **Type**,
  * where
  *   - *trace*: *P*[*A* + *C*,*B* + *C*] → *P*[*A*,*B*] is the cocartesian trace operation.
  *
  * @note A cocartesian traced promonad is a special case of a cocartesian costrong profunctor, with additional
  *   tightening and superposing laws.
  */
trait CocartesianTracedPromonad extends Promonad {
  type Self[_, _]
  type P = Self

  extension [A, B, C](self: P[Either[A, C], Either[B, C]])
    /** Traces out the parameter *C*, yielding a morphism in *P*[*A*,*B*].
      *
      * Naturality:
      *   - `self.dimap(f +++ identity, g +++ identity).cotrace == self.cotrace.dimap(f, g)`
      *
      * Dinaturality (Sliding):
      *   - `self.lmap(identity +++ h).cotrace == self.rmap(identity +++ h).cotrace`
      *
      * Tightening:
      *   - `(unit(f +++ identity) >>> self >>> unit(g +++ identity)).cotrace == unit(f) >>> self.cotrace >>> unit(g)`
      *   - *((g ⊕ id) ∘ self ∘ (f ⊕ id))* cotraced = *g ∘ self.cotrace ∘ f*
      *
      * Unitality:
      *   - `self.dimap(Left.apply, { case Left(b) => b; case Right(n) => n }).cotrace == self`
      *
      * Associativity:
      *   - `self.dimap(assoc, unassoc).cotrace.cotrace == self.cotrace`
      *
      * Superposing:
      *   - Cotracing preserves direct sums with independent computations
      *
      * Here ∘ is the composition of the category induced by *P*.
      */
    def trace: P[A, B]
}

object CocartesianTracedPromonad {

  /** Summons the `CocartesianTracedPromonad` instance of `P`. */
  def apply[P[_, _]: CocartesianTracedPromonad]: P is CocartesianTracedPromonad = {
    summon
  }
}
