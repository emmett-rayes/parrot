package parrot

/** An Elgot endopromonad over **Type**.
  *
  * Represents a promonad *P* equipped with an iteration operator with respect to the coproduct + on **Type**, where
  *   - _^†: *P*[*A*,*B* + *A*] → *P*[*A*,*B*] is the Elgot iteration operation.
  *
  * @note ElgotPromonads induce a CocartesianTracedPromonad (see
  *   [[CocartesianTracedPromonad.ElgotPromonadIsCocartesianTracedPromonad]]).
  */
trait ElgotPromonad extends Promonad {
  type Self[_, _]
  type P = Self

  extension [A, B](self: P[A, Either[B, A]])
    /** Maps a step morphism *p* in *P*[*A*,*B* + *A*] to an iterated morphism *p*^† in *P*[*A*,*B*].
      *
      * Fixpoint Property:
      *   - *p*^† = [*id*,*p*^†] ∘ *p*
      *     - `self >>> self.dagger.right >>> unit(_.merge) == self.dagger`
      *
      * Naturality in parameters:
      *   - *g* ∘ *p*^† = ((*g* + *id*) ∘ *p*)^†
      *     - `self.dagger >>> unit(g) == (self >>> unit(_.left.map(g))).dagger`
      *
      * Dinaturality (Composition Identity):
      *   - ((*id* + *g*) ∘ *f*)^† = (*id* + ((*id* + *f*) ∘ *g*)^†) ∘ *f*
      *     - `(self >>> unit(_.map(g))).dagger == self >>> unit(_.map(g.andThen(Left.apply))) >>> unit(identity)`
      *
      * Codiagonal (Double dagger):
      *   - (*p*^†)^† = ((*id* + ∇) ∘ *p*)^†
      *     - `self.dagger.dagger == (self >>> unit(_.map(_.merge))).dagger`
      *
      * Uniformity (Simulation):
      *   - If (*id* + *h*) ∘ *p* = *q* ∘ *h*, then *p*^† = *q*^† ∘ *h*
      *     - `self >>> unit(_.map(h)) == unit(h) >>> other ==> (self.dagger == unit(h) >>> other.dagger)`
      *
      * Here ∘ is the composition of the category induced by *P*, and
      *   - [*f*,*g*]: *A* + *B* → *C* is copairing / case analysis
      *   - ∇: *A* + *A* → *A* is the codiagonal morphism `[id,id]`
      *   - ι₁: *A* → *A* + *B* and ι₂: *B* → *A* + *B* are canonical coproduct injections (`Left` and `Right`)
      */
    def dagger: P[A, B]
}

object ElgotPromonad {

  /** Summons the `ElgotPromonad` instance of `P`. */
  def apply[P[_, _]: ElgotPromonad]: P is ElgotPromonad = {
    summon
  }
}
