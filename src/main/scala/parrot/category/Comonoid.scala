package parrot
package category

/** A comonoid object in a monoidal category (**V**, ⊗, *I*).
  *
  * Represents a comonoid (*C*, *ε*, *δ*), where
  *   - *C* is an object of **V**
  *   - *ε*: *C* → *I* is the counit
  *   - *δ*: *C* → *C* ⊗ *C* is the comultiplication
  */
abstract class Comonoid(tracked val monoidal: Monoidal) extends caps.Pure {
  import monoidal.{I, `*`, ***}
  import monoidal.category.{Obj, -->, >>>}

  type Self

  /** The carrier *C*. */
  final type C = Self

  /** *C* is an object of **V**.
    */
  def carrier: C is Obj

  private given CIsObj: (C is Obj) = carrier

  private given IIsObj: (I is Obj) = monoidal.unit.evidence

  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = monoidal.tensor.objects[A, B]

  /** The counit *ε*: *C* → *I*. */
  def counit: C --> I

  /** The comultiplication *δ*: *C* → *C* ⊗ *C*. */
  def comultiply: C --> (C * C)

  /** Laws that any `Comonoid` must satisfy. */
  object ComonoidLaws {

    /** (*ε* ⊗ *id*) ∘ *δ* = *λ*⁻¹
      */
    def leftCounit(using (C --> (I * C)) is Observable): Boolean = {
      (comultiply >>> (counit *** monoidal.category.identity[C])) =?= monoidal.leftUnitor[C].from
    }

    /** (*id* ⊗ *ε*) ∘ *δ* = *ρ*⁻¹
      */
    def rightCounit(using (C --> (C * I)) is Observable): Boolean = {
      (comultiply >>> (monoidal.category.identity[C] *** counit)) =?= monoidal.rightUnitor[C].from
    }

    /** *α* ∘ (*δ* ⊗ *id*) ∘ *δ* = (*id* ⊗ *δ*) ∘ *δ*
      */
    def coassociativity(using (C --> (C * (C * C))) is Observable): Boolean = {
      (comultiply >>> (comultiply *** monoidal.category.identity[C]) >>> monoidal.associator[C, C, C].to) =?=
        (comultiply >>> (monoidal.category.identity[C] *** comultiply))
    }
  }
}

object Comonoid {

  /** The comonoid objects in a monoidal category **V**. */
  type In[V <: Monoidal] = Comonoid { val monoidal: V }
}
