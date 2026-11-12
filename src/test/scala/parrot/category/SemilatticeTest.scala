package parrot
package category

import Sample.given
import Category.Type

/** The laws of [[Semilattice]] for semilattices in 𝒮. */
abstract class SemilatticeSpec(
  name: String,
  tracked override val monoid: Semilattice.In[Total.Products.type],
)(using S: Sample[monoid.M])
    extends CommutativeMonoidSpec(name, monoid, "Semilattice") {
  import monoid.M
  import monoid.SemilatticeLaws.*

  law("idempotence") {
    val observations = TotalFixture.observe[M, M]

    forAll(observations) { observe =>
      given ((M -> M) is Observable) = observe
      idempotence
    }
  }
}

/** Booleans under disjunction: a semilattice with least element `false`. */
object BooleanOr extends Semilattice(Total.Products) {
  type Self = Boolean

  def evidence: Boolean is Type = Type.TIsType

  def unit: Unit -> Boolean = {
    _ => false
  }

  def multiply: ((Boolean, Boolean)) -> Boolean = {
    (a, b) => a || b
  }
}

/** Integers under maximum: a semilattice with least element `Int.MinValue`. */
object IntMax extends Semilattice(Total.Products) {
  type Self = Int

  def evidence: Int is Type = Type.TIsType

  def unit: Unit -> Int = {
    _ => Int.MinValue
  }

  def multiply: ((Int, Int)) -> Int = {
    (a, b) => a.max(b)
  }
}

/** String concatenation, wrongly claimed to be a semilattice; the counterexample tests refute the claim. */
object ConcatClaimedSemilattice extends Semilattice(Total.Products) {
  type Self = String

  def evidence: String is Type = Type.TIsType

  def unit: Unit -> String = StringConcat.unit

  def multiply: ((String, String)) -> String = StringConcat.multiply
}

class BooleanOrIsSemilatticeTest extends SemilatticeSpec("Boolean disjunction", BooleanOr)
class IntMaxIsSemilatticeTest    extends SemilatticeSpec("Int maximum", IntMax)

class StringConcatIsNotSemilatticeTest extends LawSuite("Semilattice", "String concatenation") {
  import ConcatClaimedSemilattice.SemilatticeLaws.*

  also("CommutativeMonoid") {
    counterexample("commutativity") {
      val observations = TotalFixture.observe[(String, String), String]

      forAll(observations) { observe =>
        given ((((String, String)) -> String) is Observable) = observe
        ConcatClaimedSemilattice.CommutativeMonoidLaws.commutativity
      }
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
