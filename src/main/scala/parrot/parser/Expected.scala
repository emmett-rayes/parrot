package parrot
package parser

import category.*

/** Something a parser expected: a `label` (a literal, a pattern or a rule name), in the `context` of the rules that
  * enclosed it, innermost first.
  */
final case class Expectation(label: String, context: List[String]) derives CanEqual {

  override def toString: String = {
    if context.isEmpty then label else s"$label (in ${context.mkString(" in ")})"
  }
}

/** What a parse expected at the furthest position where something failed: the diagnostics of a parse.
  *
  * Diagnostics form a join-semilattice, where
  *   - ⊥ = (−1,∅): nothing was expected
  *   - (*p*,*X*) ⊔ (*q*,*Y*) keeps the further position, and unites the expectations at equal positions
  *
  * The laws of parsers force most of this structure: ordered choice is associative only if ⊔ is, and choice distributes
  * over a parser before it, which then runs twice, only if *x* ⊔ *y* ⊔ *x* = *x* ⊔ *y*, so in particular ⊔ is
  * idempotent. Commutativity is a choice: it makes the report independent of the order in which alternatives were
  * tried.
  */
final case class Expected(position: Int, expectations: Set[Expectation]) derives CanEqual {

  /** The join ⊔: the further position wins; at equal positions the expectations are united. */
  def join(that: Expected): Expected = {
    if position > that.position then this
    else if that.position > position then that
    else Expected(position, expectations ++ that.expectations)
  }

  /** Pushes `rule` onto the context of every expectation. Tagging preserves joins. */
  def tag(rule: String): Expected = {
    Expected(position, expectations.map(e => Expectation(e.label, rule :: e.context)))
  }

  /** The expectations, rendered in a deterministic order. */
  def describe: String = {
    expectations.toList.map(_.toString).sorted.mkString(" or ")
  }
}

object Expected {

  /** ⊥: nothing was expected. */
  val bottom: Expected = Expected(-1, Set.empty)

  /** Expecting `label` at `position`, outside any rule. */
  def at(position: Int, label: String): Expected = {
    Expected(position, Set(Expectation(label, Nil)))
  }

  /** Diagnostics are compared as data: positions and sets of expectations. */
  given ExpectedIsEq: (Expected is Eq) = Eq.structural

  /** Diagnostics form a semilattice in 𝒮. */
  object Furthest extends Semilattice(Total.Product) {
    type Self = Expected

    def carrier: Expected is Type = Type.TIsType

    def unit: Unit -> Expected = {
      _ => bottom
    }

    def multiply: ((Expected, Expected)) -> Expected = {
      (a, b) => a.join(b)
    }
  }

  /** The order of the semilattice: *a* ⊑ *b* when *b* carries at least the information of *a*. */
  given ExpectedIsPreorder: (Expected is Preorder) = Preorder.of(Furthest)
}
