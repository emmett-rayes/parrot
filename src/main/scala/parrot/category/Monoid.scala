package parrot
package category

/** A monoid object in a monoidal category (**V**, ⊗, *I*).
  *
  * Represents a monoid (*M*, *η*, *μ*), where
  *   - *M* is an object of **V**
  *   - *η*: *I* → *M* is the unit
  *   - *μ*: *M* ⊗ *M* → *M* is the multiplication
  */
abstract class Monoid(tracked val V: Monoidal) extends caps.Pure {
  import V.{I, `*`, ***, given}
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
