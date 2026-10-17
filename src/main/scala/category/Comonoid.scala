package parrot
package category

import category.Monoidal.on

/** A comonoid object on an underlying monoidal category **C**.
  *
  * Represents a comonoid object (*M*, *δ*, *ε*) in (**C**, ⊗, *I*), where
  *   - *ε*: *M* ~> *I* is the counit morphism
  *   - *δ*: *M* ~> *M* ⊗ *M* is the comultiplication morphism
  */
trait Comonoid {
  type Self
  final type M = Self

  type In[_, _]: Monoidal on PureFunction as ComonoidInMonoidal

  val InIsMonoidal: In is Monoidal on PureFunction = ComonoidInMonoidal

  import InIsMonoidal.*
  import InIsMonoidal.SelfIsPromonad.*

  /** The counit morphism *ε*: *M* ~> *I*. */
  def zero: M ~> I

  /** The comultiplication morphism *δ*: *M* ~> *M* ⊗ *M*. */
  def add: M ~> (M * M)

  /** Laws that any `Comonoid` must satisfy. */
  object ComonoidLaws {

    /** (*ε* ⊗ *id*_M) ∘ *δ* = *λ*⁻¹_M
      */
    def leftIdentity(using M ~> (I * M) is Eq): Boolean = {
      (add >>> (zero *** identity[M])) === leftUnitorInv[M]
    }

    /** (*id*_M ⊗ *ε*) ∘ *δ* = *ρ*⁻¹_M
      */
    def rightIdentity(using M ~> (M * I) is Eq): Boolean = {
      (add >>> (identity[M] *** zero)) === rightUnitorInv[M]
    }

    /** *α*_{M,M,M} ∘ (*δ* ⊗ *id*_M) ∘ *δ* = (*id*_M ⊗ *δ*) ∘ *δ*
      */
    def coassociativity(using M ~> (M * (M * M)) is Eq): Boolean = {
      (add >>> (add *** identity[M]) >>> associate[M, M, M]) === (add >>> (identity[M] *** add))
    }
  }
}

object Comonoid {

  /** Refines the `In` type of `Comonoid` to the monoidal `K` with unit `U` and tensor `T`. */
  type in[K[_, _], U, T[_, _]] = Comonoid {
    type In = K
    val InIsMonoidal: (K is Monoidal.`with`[U, T]) on PureFunction
  }

  /** Summons the `Comonoid` instance of `M`. */
  def apply[M: Comonoid]: M is Comonoid = summon
}
