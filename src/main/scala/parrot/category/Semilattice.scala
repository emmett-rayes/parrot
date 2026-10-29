package parrot
package category

/** A semilattice in a cartesian category.
  *
  * Represents a commutative monoid (*M*, ⊥, ⊔) with idempotent multiplication, where
  *   - ⊔ ∘ *β* = ⊔: the order of arguments does not matter
  *   - ⊔ ∘ Δ = *id*: combining a value with itself changes nothing
  *
  * The induced preorder *a* ⊑ *b* ⇔ *a* ⊔ *b* = *b* has ⊔ as join and the unit ⊥ as least element.
  */
abstract class Semilattice(tracked override val V: Cartesian) extends Monoid(V) {
  import V.{*, given}
  import V.K.{Obj, -->, >>>}

  private given MIsObj: (M is Obj) = carrier

  /** Laws that any `Semilattice` must satisfy. */
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
