package parrot

/** An endopromonad over **Type**.
  *
  * Represents a monoid in the monoidal category of endoprofunctors **Prof** over **Type**, where
  *   - *Hom*, the hom-profunctor, the unit object of **Prof**
  *   - ⋄ is the tensor product of **Prof**
  *   - *η*: *Hom* ⇒ *P* is the unit of the monoid
  *   - *μ*: *P* ⋄ *P* ⇒ *P* is the multiplication of the monoid
  */
trait Promonad extends Profunctor {
  type Self[_, _]
  type P = Self

  /** The unit natural transformation *η*: *Hom* ⇒ *P*.
    *
    * Maps a morphism *f*: *A* → *B* to an element *η*(*f*) in *P*[*A*,*B*].
    *
    * Naturality:
    *   - *P*(*h*,*k*) ∘ *η* = *η* ∘ *Hom*(*h*,*k*)
    *     - `unit(f).dimap(h, k) == unit(h andThen f andThen k)`
    *
    * Unitality:
    *   - left identity: *μ*(*η*(*id*),*p*) = *p*
    *     - `unit(identity).combine(p) == p`
    *   - right identity: *μ*(*p*,*η*(*id*)) = *p*
    *     - `p.combine(unit(identity)) == p`
    */
  def unit[A, B](f: A => B): P[A, B]

  extension [A, B](self: P[A, B])
    /** The multiplication natural transformation *μ*: *P* ⋄ *P* ⇒ *P*.
      *
      * Maps an element *p* in *P*[*A*,*B*] and *q* in *P*[*B*,*C*] to an element *μ*(*p*,*q*) in *P*[*A*,*C*].
      *
      * Naturality:
      *   - *P*(*h*,*k*)(*μ*(*p*,*q*)) = *μ*(*P*(*h*,*id*)(*p*),*P*(*id*,*k*)(*q*))
      *     - `self.combine(other).dimap(h, k) == self.lmap(h).combine(other.rmap(k))`
      *
      * Associativity:
      *   - *μ*(*μ*(*p*,*q*),*r*) = *μ*(*p*,*μ*(*q*,*r*))
      *     - `self.combine(other1).combine(other2) == self.combine(other1.combine(other2))`
      */
    def combine[C](other: P[B, C]): P[A, C]

  extension [B, C](self: P[B, C])
    def dimap[A, D](f: A => B, g: C => D): P[A, D] = {
      unit(f).combine(self.combine(unit(g)))
    }

  extension [A, B](self: P[A, B])
    /** Alias for [[combine]]. */
    def >>>[C](other: P[B, C]): P[A, C] = {
      self.combine(other)
    }
}

object Promonad {

  /** Summons the `Promonad` instance of `P`. */
  def apply[P[_, _]: Promonad]: P is Promonad = {
    summon
  }

  /** Every promonad induces a category, where
    *   - *A* ~> *B* = *P*[*A*,*B*] are the hom-sets
    *   - *id* = *η*(*id*) is the identity morphism
    *   - *g* ∘ *f* = *μ*(*f*,*g*) is composition
    */
  given PromonadIsCategory: [P[_, _]: Promonad] => P is Category {
    def id[A]: A ~> A = {
      P.unit(identity)
    }

    extension [B, C](self: B ~> C)
      def compose[A](other: A ~> B): A ~> C = {
        other.combine(self)
      }
  }
}
