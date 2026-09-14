package parrot

/** A restriction endopromonad over **Type**.
  *
  * Represents a promonad *P* equipped with a restriction structure, where
  *   - _̅: *P*[*A*, *B*] → *P*[*A*, *A*] is the restriction operation
  */
trait RestrictionPromonad extends Promonad {
  type Self[_, _]
  type P = Self

  extension [A, B](self: P[A, B])
    /** Maps an element *p* in *P*[*A*, *B*] to an element *p̅* in *P*[*A*, *A*].
      *
      * Restriction:
      *   - *p* ∘ *p̅* = *p*
      *     - `self.restrict >>> self == self`
      *
      * Commutativity:
      *   - *q̅* ∘ *p̅* = *p̅* ∘ *q̅*
      *     - `self.restrict >>> other.restrict == other.restrict >>> self.restrict`
      *
      * Absorption:
      *   - *(q ∘ p̅)̅* = *q̅* ∘ *p̅*
      *     - `(self.restrict >>> other).restrict == self.restrict >>> other.restrict`
      *
      * Lax Naturality:
      *   - *q̅* ∘ *p* = *p* ∘ *(q ∘ p)̅*
      *     - `self >>> other.restrict == (self >>> other).restrict >>> self`
      *
      * Here ∘ is the composition of the category induced by *P*.
      */
    def restrict: P[A, A]
}

object RestrictionPromonad {

  /** Summons the `RestrictionPromonad` instance of `P`. */
  def apply[P[_, _]: RestrictionPromonad]: P is RestrictionPromonad = {
    summon
  }
}
