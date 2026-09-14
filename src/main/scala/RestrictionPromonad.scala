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
      *   - *p̅* ; *p* = *p*
      *     - `self.restrict.combine(self) == self`
      *
      * Commutativity:
      *   - *p̅* ; *q̅* = *q̅* ; *p̅*
      *     - `self.restrict.combine(other.restrict) == other.restrict.combine(self.restrict)`
      *
      * Absorption:
      *   - *(p̅ ; q)̅* = *p̅* ; *q̅*
      *     - `self.restrict.combine(other).restrict == self.restrict.combine(other.restrict)`
      *
      * Lax Naturality:
      *   - *p* ; *q̅* = *(p ; q)̅* ; *p*
      *     - `self.combine(other.restrict) == self.combine(other).restrict.combine(self)`
      *
      * Here ; is the multiplication of *P*.
      */
    def restrict: P[A, A]
}

object RestrictionPromonad {

  /** Summons the `RestrictionPromonad` instance of `P`. */
  def apply[P[_, _]: RestrictionPromonad]: P is RestrictionPromonad = {
    summon
  }
}
