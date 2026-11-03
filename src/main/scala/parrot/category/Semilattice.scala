package parrot
package category

/** A semilattice in a cartesian category.
  *
  * Represents a commutative monoid (*M*, ⊥, ⊔), where
  *   - ⊥ is the unit
  *   - ⊔ is commutative and idempotent
  *
  * The induced preorder *a* ⊑ *b* ⇔ *a* ⊔ *b* = *b* has ⊔ as join and the unit ⊥ as least element.
  */
abstract class Semilattice(tracked override val monoidal: Cartesian) extends Monoid(monoidal) {
  import monoidal.`*`
  import monoidal.category.{Obj, identity, -->, >>>}

  private given MIsObj: (M is Obj)                                = evidence
  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = monoidal.tensor.objects[A, B]

  /** Laws that any `Semilattice` must satisfy. */
  object SemilatticeLaws {

    /** ⊔ ∘ *σ* = ⊔ */
    def commutativity(using ((M * M) --> M) is Observable): Boolean = {
      (monoidal.braid[M, M] >>> multiply) =?= multiply
    }

    /** ⊔ ∘ Δ = *id* */
    def idempotence(using (M --> M) is Observable): Boolean = {
      (monoidal.diagonal[M] >>> multiply) =?= identity[M]
    }
  }
}

object Semilattice {

  /** The semilattices in a cartesian category **V**. */
  type In[V <: Cartesian] = Semilattice { val monoidal: V }
}
