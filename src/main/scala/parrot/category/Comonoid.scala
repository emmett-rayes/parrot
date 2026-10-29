package parrot
package category

/** A comonoid object in a monoidal category (**V**, ⊗, *I*).
  *
  * Represents a comonoid (*C*, *ε*, *δ*), where
  *   - *C* is an object of **V**
  *   - *ε*: *C* → *I* is the counit
  *   - *δ*: *C* → *C* ⊗ *C* is the comultiplication
  */
abstract class Comonoid(tracked val V: Monoidal) extends caps.Pure {
  import V.{I, `*`, ***, given}
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
