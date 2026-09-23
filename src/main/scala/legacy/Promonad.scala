package parrot
package legacy

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
    *     - `unit(identity) >>> p == p`
    *   - right identity: *μ*(*p*,*η*(*id*)) = *p*
    *     - `p >>> unit(identity) == p`
    */
  def unit[A, B](f: A => B): P[A, B]

  extension [A, B](self: P[A, B])
    /** The multiplication natural transformation *μ*: *P* ⋄ *P* ⇒ *P*.
      *
      * Maps an element *p* in *P*[*A*,*B*] and *q* in *P*[*B*,*C*] to an element *μ*(*p*,*q*) in *P*[*A*,*C*].
      *
      * Naturality:
      *   - *P*(*h*,*k*)(*μ*(*p*,*q*)) = *μ*(*P*(*h*,*id*)(*p*),*P*(*id*,*k*)(*q*))
      *     - `(self >>> other).dimap(h, k) == self.lmap(h) >>> other.rmap(k)`
      *
      * Associativity:
      *   - *μ*(*μ*(*p*,*q*),*r*) = *μ*(*p*,*μ*(*q*,*r*))
      *     - `(self >>> other1) >>> other2 == self >>> (other1 >>> other2)`
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

  /** Every cartesian strong promonad induces a cartesian monoidal profunctor, where
    *   - *unit* = *η*(*id*) is the unit element
    *   - *p* ⊗ *q* = *second*(*q*) ∘ *first*(*p*) is the tensor product
    *
    * Here *η* is the unit of *P* and ∘ is the composition of the category induced by *P*.
    */
  given PromonadIsCartesianMonoidalProfunctor
    : [P[_, _]: Promonad] => (F: P is CartesianStrongProfunctor) => P is CartesianMonoidalProfunctor {
    export F.dimap

    def unit: P[Unit, Unit] = {
      P.unit(identity)
    }

    extension [A, B](self: P[A, B])
      def tensor[C, D](other: P[C, D]): P[(A, C), (B, D)] = {
        self.first.combine(other.second)
      }
  }

  /** Every cocartesian strong promonad induces a cocartesian monoidal profunctor, where
    *   - *empty* = *η*(*id*) is the unit element
    *   - *p* ⊕ *q* = *right*(*q*) ∘ *left*(*p*) is the sum
    *
    * Here *η* is the unit of *P* and ∘ is the composition of the category induced by *P*.
    */
  given PromonadIsCocartesianMonoidalProfunctor
    : [P[_, _]: Promonad] => (F: P is CocartesianStrongProfunctor) => P is CocartesianMonoidalProfunctor {
    export F.dimap

    def empty: P[Nothing, Nothing] = {
      P.unit(identity)
    }

    extension [A, B](self: P[A, B])
      def sum[C, D](other: P[C, D]): P[Either[A, C], Either[B, D]] = {
        self.left.combine(other.right)
      }
  }
}
