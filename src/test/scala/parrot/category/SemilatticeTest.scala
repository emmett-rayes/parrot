package parrot
package category

import Sample.given

/** The laws of [[Semilattice]] for semilattices in 𝒮. */
abstract class SemilatticeSpec(name: String, tracked val W: Semilattice { val V: Total.Product.type })(
  using S: Sample[W.M]
) extends LawSuite("Semilattice", name) {
  import W.M
  import W.V.`*`
  import W.SemilatticeLaws.*

  law("commutativity") {
    val observations = TotalFixture.observe[M * M, M]

    forAll(observations) { observe =>
      given (((M * M) -> M) is Observable) = observe
      commutativity
    }
  }

  law("idempotence") {
    val observations = TotalFixture.observe[M, M]

    forAll(observations) { observe =>
      given ((M -> M) is Observable) = observe
      idempotence
    }
  }
}

/** Booleans under disjunction: a semilattice with least element `false`. */
object BooleanOr extends Semilattice(Total.Product) {
  type Self = Boolean

  def carrier: Boolean is Type = Type.TIsType

  def unit: Unit -> Boolean = {
    _ => false
  }

  def multiply: ((Boolean, Boolean)) -> Boolean = {
    (a, b) => a || b
  }
}

/** Integers under maximum: a semilattice with least element `Int.MinValue`. */
object IntMax extends Semilattice(Total.Product) {
  type Self = Int

  def carrier: Int is Type = Type.TIsType

  def unit: Unit -> Int = {
    _ => Int.MinValue
  }

  def multiply: ((Int, Int)) -> Int = {
    (a, b) => a.max(b)
  }
}

/** String concatenation, wrongly claimed to be a semilattice; the counterexample tests refute the claim. */
object ConcatClaimedSemilattice extends Semilattice(Total.Product) {
  type Self = String

  def carrier: String is Type = Type.TIsType

  def unit: Unit -> String = StringConcat.unit

  def multiply: ((String, String)) -> String = StringConcat.multiply
}

class BooleanOrIsSemilatticeTest extends SemilatticeSpec("Boolean disjunction", BooleanOr)
class IntMaxIsSemilatticeTest    extends SemilatticeSpec("Int maximum", IntMax)

class StringConcatIsNotSemilatticeTest extends LawSuite("Semilattice", "String concatenation") {
  import ConcatClaimedSemilattice.SemilatticeLaws.*

  counterexample("commutativity") {
    val observations = TotalFixture.observe[(String, String), String]

    forAll(observations) { observe =>
      given ((((String, String)) -> String) is Observable) = observe
      commutativity
    }
  }

  counterexample("idempotence") {
    val observations = TotalFixture.observe[String, String]

    forAll(observations) { observe =>
      given ((String -> String) is Observable) = observe
      idempotence
    }
  }
}
