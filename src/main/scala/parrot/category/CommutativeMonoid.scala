package parrot
package category

/** A commutative monoid object in a symmetric monoidal category (**V**, ⊗, *I*, *σ*).
  *
  * Represents a monoid (*M*, *η*, *μ*), where
  *   - *μ* is commutative: it does not depend on the order of its arguments
  *
  * Commutativity needs only the braiding. A [[Semilattice]] is a commutative monoid that is also idempotent, which
  * needs a diagonal.
  *
  * @see docs/TUTORIAL.md §15.3
  */
abstract class CommutativeMonoid(tracked override val monoidal: Symmetric) extends Monoid(monoidal) {
  import monoidal.`*`
  import monoidal.category.{Obj, -->, >>>}

  /** Laws that any `CommutativeMonoid` must satisfy. */
  object CommutativeMonoidLaws {
    private given MIsObj: (M is Obj)                                = evidence
    private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = monoidal.tensor.objects[A, B]

    /** *μ* ∘ *σ* = *μ* */
    def commutativity(using ((M * M) --> M) is Observable): Boolean = {
      (monoidal.braid[M, M] >>> multiply) =?= multiply
    }
  }
}

object CommutativeMonoid {

  /** The commutative monoid objects in a symmetric monoidal category **V**. */
  type In[V <: Symmetric] = CommutativeMonoid { val monoidal: V }
}
