package parrot
package category

/** A monoid object in a monoidal category (**V**, ⊗, *I*): an object with a unit and an associative multiplication,
  * both morphisms of **V**.
  *
  * Represents a monoid (*M*, *η*, *μ*), where
  *   - *M* is an object of **V**
  *   - *η*: *I* → *M* is the unit
  *   - *μ*: *M* ⊗ *M* → *M* is the multiplication
  *
  * In 𝒮 with pairs, this is an ordinary monoid: an element *η*(()) and a binary operation. In the endofunctors with
  * composition it would be a monad, which Scala cannot state with the same class (see [[Monad]]). The dual is
  * [[Comonoid]].
  */
abstract class Monoid(tracked val V: Monoidal) extends caps.Pure {
  import V.{*, given}
  import V.K.{Obj, -->, >>>}

  type Self

  /** The carrier *M*. */
  final type M = Self

  /** *M* is an object of **V**.
    */
  def carrier: M is Obj

  private given MIsObj: (M is Obj) = carrier

  /** The unit *η*: *I* → *M*. */
  def unit: I --> M

  /** The multiplication *μ*: *M* ⊗ *M* → *M*. */
  def multiply: (M * M) --> M

  /** Laws that any `Monoid` must satisfy. */
  object MonoidLaws {

    /** *μ* ∘ (*η* ⊗ *id*) = *λ*
      */
    def leftUnit(using ((I * M) --> M) is Observable): Boolean = {
      ((unit *** V.K.identity[M]) >>> multiply) =?= V.leftUnitor[M].to
    }

    /** *μ* ∘ (*id* ⊗ *η*) = *ρ*
      */
    def rightUnit(using ((M * I) --> M) is Observable): Boolean = {
      ((V.K.identity[M] *** unit) >>> multiply) =?= V.rightUnitor[M].to
    }

    /** *μ* ∘ (*μ* ⊗ *id*) = *μ* ∘ (*id* ⊗ *μ*) ∘ *α*
      */
    def associativity(using (((M * M) * M) --> M) is Observable): Boolean = {
      ((multiply *** V.K.identity[M]) >>> multiply) =?=
        (V.associator[M, M, M].to >>> (V.K.identity[M] *** multiply) >>> multiply)
    }
  }
}

/** A semilattice in a cartesian category: a commutative monoid whose multiplication is idempotent.
  *
  * Represents a monoid (*M*, ⊥, ⊔), where
  *   - ⊔ ∘ *β* = ⊔: the order of arguments does not matter
  *   - ⊔ ∘ Δ = *id*: combining a value with itself changes nothing
  *
  * The induced preorder *a* ⊑ *b* ⇔ *a* ⊔ *b* = *b* has ⊔ as join and the unit ⊥ as least element: a join-semilattice
  * is a preorder with finite coproducts.
  */
abstract class Semilattice(tracked override val V: Cartesian) extends Monoid(V) {
  import V.{*, given}
  import V.K.{Obj, -->, >>>}

  private given MIsObj: (M is Obj) = carrier

  /** Laws that a `Semilattice` must satisfy beyond those of a [[Monoid]]. */
  object SemilatticeLaws {

    /** ⊔ ∘ *β* = ⊔ */
    def commutativity(using ((M * M) --> M) is Observable): Boolean = {
      (V.braid[M, M] >>> multiply) =?= multiply
    }

    /** ⊔ ∘ Δ = *id* */
    def idempotence(using (M --> M) is Observable): Boolean = {
      (V.diagonal[M] >>> multiply) =?= V.K.identity[M]
    }
  }
}

/** A comonoid object in a monoidal category (**V**, ⊗, *I*): the dual of a [[Monoid]], an object that can be deleted
  * and copied.
  *
  * Represents a comonoid (*C*, *ε*, *δ*), where
  *   - *C* is an object of **V**
  *   - *ε*: *C* → *I* is the counit, which deletes
  *   - *δ*: *C* → *C* ⊗ *C* is the comultiplication, which copies
  *
  * In a cartesian category every object is a comonoid in exactly one way, by ! and Δ ([[Cartesian.comonoid]]). The
  * converse is Fox's theorem: a symmetric monoidal category is cartesian when every object has a comonoid structure
  * that every morphism preserves. Pairs in 𝒫 have the comonoids ([[Partial.Product.comonoid]]) but not the
  * preservation: a program that does not terminate cannot be deleted.
  */
abstract class Comonoid(tracked val V: Monoidal) extends caps.Pure {
  import V.{*, given}
  import V.K.{Obj, -->, >>>}

  type Self

  /** The carrier *C*. */
  final type C = Self

  /** *C* is an object of **V**.
    */
  def carrier: C is Obj

  private given CIsObj: (C is Obj) = carrier

  /** The counit *ε*: *C* → *I*. */
  def counit: C --> I

  /** The comultiplication *δ*: *C* → *C* ⊗ *C*. */
  def comultiply: C --> (C * C)

  /** Laws that any `Comonoid` must satisfy. */
  object ComonoidLaws {

    /** (*ε* ⊗ *id*) ∘ *δ* = *λ*⁻¹
      */
    def leftCounit(using (C --> (I * C)) is Observable): Boolean = {
      (comultiply >>> (counit *** V.K.identity[C])) =?= V.leftUnitor[C].from
    }

    /** (*id* ⊗ *ε*) ∘ *δ* = *ρ*⁻¹
      */
    def rightCounit(using (C --> (C * I)) is Observable): Boolean = {
      (comultiply >>> (V.K.identity[C] *** counit)) =?= V.rightUnitor[C].from
    }

    /** *α* ∘ (*δ* ⊗ *id*) ∘ *δ* = (*id* ⊗ *δ*) ∘ *δ*
      */
    def coassociativity(using (C --> (C * (C * C))) is Observable): Boolean = {
      (comultiply >>> (comultiply *** V.K.identity[C]) >>> V.associator[C, C, C].to) =?=
        (comultiply >>> (V.K.identity[C] *** comultiply))
    }
  }
}
