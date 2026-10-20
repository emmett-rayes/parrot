package parrot
package category

import scala.annotation.targetName

/** A valued promonad on a base category **B** over a target category **V**.
  *
  * Represents a monoid *P* in the monoidal category of endoprofunctors **Prof[**V**, **V**] on **B**, where
  *   - *P* ⇒ *Q* are morphisms of **Prof** (natural transformations between profunctors)
  *   - *Hom* is the unit object of **Prof** (the Hom-profunctor)
  *   - ⋄ is the tensor product of **Prof**
  *   - *η*: *Hom* ⇒ *P* is the unit of the monoid
  *   - *μ*: *P* ⋄ *P* ⇒ *P* is the multiplication of the monoid
  */
trait Promonad extends Profunctor {
  override type V[_, _]: Monoidal as PromonadOverMonoidal

  val VIsMonoidal: V is Monoidal          = PromonadOverMonoidal
  override val VIsCategory: V is Category = PromonadOverMonoidal.SelfIsCategory

  import VIsMonoidal.*

  /** Maps a morphism *f*: *A* --> *B* in **B** to a global element *I* ->> *P*[*A*,*B*] in **V**.
    *
    * @note This is the component-wise unique representation in **V** of the unit natural transformation *η*: *Hom* ⇒
    *   *P* in **Prof** (by Yoneda).
    */
  def unit[A, B](f: A --> B): I ->> P[A, B]

  /** Maps a tensor product of hom-objects *P*[*B*,*C*] ⊗ *P*[*A*,*B*] to the composite hom-object *P*[*A*,*C*] in
    * **V**.
    *
    * @note This is the component-wise unique representation in **V** of the multiplication natural transformation *μ*:
    *   *P* ⋄ *P* ⇒ *P* in **Prof** (by the universal property of the coend).
    */
  def multiply[A, B, C]: (P[B, C] * P[A, B]) ->> P[A, C]

  override def dimap[A, B, C, D](f: C --> A, g: B --> D): (P[A, B]) ->> (P[C, D]) = {
    val weaken   = rightUnitorInv[P[A, B]] >>> (leftUnitorInv[P[A, B]] *** V.identity[I])
    val insert   = unit(g) *** V.identity[P[A, B]] *** unit(f)
    val contract = (multiply[A, B, D] *** V.identity[P[C, A]]) >>> multiply[C, A, D]
    weaken >>> insert >>> contract
  }

  /** The morphisms of the underlying ordinary category induced by this promonad. */
  type Underlying[A, B] = I ->> P[A, B]

  /** Every promonad on **B** induces a **V**-enriched category with objects *Ob*(**B**) and hom-objects *P*[*A*,*B*],
    * where
    *   - *J*: **B** → *P* = *f* ↦ *η*(*f*) is the identity-on-objects functor given on morphisms by the unit *η*
    *   - *id* : *I* ->> *P*[*A*,*A*] is the identity morphism in **V**
    *   - ∘ : (*P*[*B*,*C*] ⊗ *P*[*A*,*B*]) ->> *P*[*A*,*C*] is the composition morphism in **V**
    */
  given PromonadIsCategory: Underlying is Category {
    def identity[A]: I ->> P[A, A] = {
      unit(B.identity[A])
    }

    def compose[A, B, C](p: I ->> P[B, C], q: I ->> P[A, B]): I ->> P[A, C] = {
      leftUnitorInv[I] >>> (p *** q) >>> multiply[A, B, C]
    }
  }

  /** Laws that any `Promonad` must satisfy. */
  object PromonadLaws {

    /** *P*(*h*, *k*) ∘ *η* = *η* ∘ *Hom*(*h*, *k*)
      */
    def unitNaturality[A, B, C, D](
      f: A --> B,
      h: C --> A,
      k: B --> D,
    )(using (I ->> P[C, D]) is Eq): Boolean = {
      unit(h >>> f >>> k) === unit(f) >>> dimap(h, k)
    }

    /** *P*(*h*, *k*) ∘ *μ* = *μ* ∘ (*P*(*id*, *k*) ⊗ *P*(*h*, *id*))
      */
    def multiplicationNaturality[A, B, C, D, E](
      h: D --> A,
      k: C --> E,
    )(using ((P[B, C] * P[A, B]) ->> P[D, E]) is Eq): Boolean = {
      (multiply[A, B, C] >>> dimap(h, k)) === ((rmap(k) *** lmap(h)) >>> multiply[D, B, E])
    }

    /** *μ* ∘ (*η*(*id*) ⊗ *id*) ∘ *λ*⁻¹ = *id*
      */
    def leftIdentity[A, B](using (P[A, B] ->> P[A, B]) is Eq): Boolean = {
      val lhs = leftUnitorInv[P[A, B]] >>> (unit(B.identity[B]) *** V.identity[P[A, B]]) >>>
        multiply[A, B, B]
      lhs === V.identity[P[A, B]]
    }

    /** *μ* ∘ (*id* ⊗ *η*(*id*)) ∘ *ρ*⁻¹ = *id*
      */
    def rightIdentity[A, B](using (P[A, B] ->> P[A, B]) is Eq): Boolean = {
      val lhs = rightUnitorInv[P[A, B]] >>> (V.identity[P[A, B]] *** unit(B.identity[A])) >>>
        multiply[A, A, B]
      lhs === V.identity[P[A, B]]
    }

    /** *μ* ∘ (*id* ⊗ *μ*) ∘ *α* = *μ* ∘ (*μ* ⊗ *id*)
      */
    def associativity[A, B, C, D](using
      (((P[C, D] * P[B, C]) * P[A, B]) ->> P[A, D]) is Eq
    ): Boolean = {
      val lhs = associate[P[C, D], P[B, C], P[A, B]] >>> (V.identity[P[C, D]] *** multiply[A, B, C]) >>>
        multiply[A, C, D]
      val rhs = (multiply[B, C, D] *** V.identity[P[A, B]]) >>> multiply[A, B, D]
      lhs === rhs
    }

    /** *μ* ∘ (*id* ⊗ *P*(*id*, *f*)) = *μ* ∘ (*P*(*f*, *id*) ⊗ *id*)
      */
    def wedge[A, B, BPrime, C](
      f: BPrime --> B,
    )(using ((P[B, C] * P[A, BPrime]) ->> P[A, C]) is Eq): Boolean = {
      val lhs = (V.identity[P[B, C]] *** rmap(f)) >>> multiply[A, B, C]
      val rhs = (lmap(f) *** V.identity[P[A, BPrime]]) >>> multiply[A, BPrime, C]
      lhs === rhs
    }
  }
}

object Promonad {

  /** Refines the base category `B` of `Promonad` to `T`. */
  infix type on[P <: Promonad, T[_, _]] = P { type B = T }

  /** Refines the target category `V` of `Promonad` to `T`. */
  infix type over[P <: Promonad, T[_, _]] = P { type V = T }

  /** Summons the `Promonad` instance of `P`. */
  def apply[P[_, _]: Promonad]: P is Promonad = summon

  /** `Promonad` instance for `=:=` on the discrete category *Ob*(**Type**) over **Type**. */
  given TypeEqIsPromonad: =:= is Promonad {
    type B = =:=
    type V = Function

    override given ProfunctorOnCategory: Category.TypeEqIsCategory.type = Category.TypeEqIsCategory
    override val BIsCategory: Category.TypeEqIsCategory.type            = Category.TypeEqIsCategory

    override given ProfunctorOverCategory: Category.FunctionIsCategory.type = Category.FunctionIsCategory
    override val VIsCategory: Category.FunctionIsCategory.type              = Category.FunctionIsCategory

    override given PromonadOverMonoidal: Monoidal.FunctionIsMonoidal.type = Monoidal.FunctionIsMonoidal
    override val VIsMonoidal: Monoidal.FunctionIsMonoidal.type            = Monoidal.FunctionIsMonoidal

    def unit[A, B](f: A =:= B): Unit => (A =:= B) = {
      _ => f
    }

    def multiply[A, B, C]: ((B =:= C, A =:= B)) => (A =:= C) = {
      case (q, p) => q.substituteCo(p)
    }

    override def dimap[A, B, C, D](f: C =:= A, g: B =:= D): (A =:= B) => (C =:= D) = {
      p => g.substituteCo(p.substituteCo(f))
    }
  }

  /** `Promonad` instance for `Function` on the category **Type** over **Type**. */
  given FunctionIsPromonad: Function is Promonad {
    type B = Function
    type V = Function

    override given ProfunctorOnCategory: Category.FunctionIsCategory.type = Category.FunctionIsCategory
    override val BIsCategory: Category.FunctionIsCategory.type            = Category.FunctionIsCategory

    override given ProfunctorOverCategory: Category.FunctionIsCategory.type = Category.FunctionIsCategory
    override val VIsCategory: Category.FunctionIsCategory.type              = Category.FunctionIsCategory

    override given PromonadOverMonoidal: Monoidal.FunctionIsMonoidal.type = Monoidal.FunctionIsMonoidal
    override val VIsMonoidal: Monoidal.FunctionIsMonoidal.type            = Monoidal.FunctionIsMonoidal

    def unit[A, B](f: A => B): Unit => (A => B) = {
      _ => f
    }

    def multiply[A, B, C]: ((B => C, A => B)) => (A => C) = {
      case (q, p) => a => q(p(a))
    }

    override def dimap[A, B, C, D](f: C => A, g: B => D): (A => B) => (C => D) = {
      p => f.andThen(p.andThen(g))
    }
  }
}
