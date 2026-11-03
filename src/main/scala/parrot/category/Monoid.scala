package parrot
package category

/** A monoid object in a monoidal category (**V**, ⊗, *I*).
  *
  * Represents a monoid (*M*, *η*, *μ*), where
  *   - *M* is an object of **V**
  *   - *η*: *I* → *M* is the unit
  *   - *μ*: *M* ⊗ *M* → *M* is the multiplication
  */
abstract class Monoid(tracked val monoidal: Monoidal) extends Category.Object(monoidal.category) {
  import monoidal.{I, `*`, ***}
  import monoidal.category.{Obj, identity, -->, >>>}

  /** The monoid object *M*. */
  final type M = Self

  private given MIsObj: (M is Obj)                                = evidence
  private given IIsObj: (I is Obj)                                = monoidal.unit.evidence
  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = monoidal.tensor.objects[A, B]

  /** The unit *η*: *I* → *M*. */
  def unit: I --> M

  /** The multiplication *μ*: *M* ⊗ *M* → *M*. */
  def multiply: (M * M) --> M

  /** Laws that any `Monoid` must satisfy. */
  object MonoidLaws {

    /** *μ* ∘ (*η* ⊗ *id*) = *λ*
      */
    def leftUnit(using ((I * M) --> M) is Observable): Boolean = {
      ((unit *** identity[M]) >>> multiply) =?= monoidal.leftUnitor[M].to
    }

    /** *μ* ∘ (*id* ⊗ *η*) = *ρ*
      */
    def rightUnit(using ((M * I) --> M) is Observable): Boolean = {
      ((identity[M] *** unit) >>> multiply) =?= monoidal.rightUnitor[M].to
    }

    /** *μ* ∘ (*μ* ⊗ *id*) = *μ* ∘ (*id* ⊗ *μ*) ∘ *α*
      */
    def associativity(using (((M * M) * M) --> M) is Observable): Boolean = {
      ((multiply *** identity[M]) >>> multiply)
        =?= (monoidal.associator[M, M, M].to >>> (identity[M] *** multiply) >>> multiply)
    }
  }
}

object Monoid {

  /** The monoid objects in a monoidal category **V**. */
  type In[V <: Monoidal] = Monoid { val monoidal: V }
}
