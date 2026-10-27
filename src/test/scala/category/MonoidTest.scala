package parrot
package category

import Sample.given

/** Strings under concatenation: a monoid in 𝒮 that is neither commutative nor idempotent. */
object StringConcat extends Monoid(Total.Product) {
  type Self = String

  def carrier: String is Type = Type.TIsType

  def unit: Unit -> String = {
    _ => ""
  }

  def multiply: ((String, String)) -> String = {
    (a, b) => a + b
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

/** The laws of [[Monoid]] for monoids in 𝒮 with pairs. */
abstract class MonoidSpec(name: String, tracked val W: Monoid { val V: Total.Product.type })(
  using S: Sample[W.M]
) extends LawSuite("Monoid", name) {
  import W.MonoidLaws.*

  law("leftUnit") {
    val observations = TotalFixture.observe[(Unit, W.M), W.M]
    forAll(observations) { observe =>
      given ((((Unit, W.M)) -> W.M) is Observable) = observe
      leftUnit
    }
  }

  law("rightUnit") {
    val observations = TotalFixture.observe[(W.M, Unit), W.M]
    forAll(observations) { observe =>
      given ((((W.M, Unit)) -> W.M) is Observable) = observe
      rightUnit
    }
  }

  law("associativity") {
    val observations = TotalFixture.observe[((W.M, W.M), W.M), W.M]
    forAll(observations) { observe =>
      given (((((W.M, W.M), W.M)) -> W.M) is Observable) = observe
      associativity
    }
  }
}

/** The laws of [[Semilattice]] for semilattices in 𝒮. */
abstract class SemilatticeSpec(name: String, tracked val W: Semilattice { val V: Total.Product.type })(
  using S: Sample[W.M]
) extends LawSuite("Semilattice", name) {
  import W.SemilatticeLaws.*

  law("commutativity") {
    val observations = TotalFixture.observe[(W.M, W.M), W.M]
    forAll(observations) { observe =>
      given ((((W.M, W.M)) -> W.M) is Observable) = observe
      commutativity
    }
  }

  law("idempotence") {
    val observations = TotalFixture.observe[W.M, W.M]
    forAll(observations) { observe =>
      given ((W.M -> W.M) is Observable) = observe
      idempotence
    }
  }
}

class StringConcatIsMonoidTest extends MonoidSpec("String concatenation", StringConcat)

class BooleanOrIsMonoidTest extends MonoidSpec("Boolean disjunction", BooleanOr)

class BooleanOrIsSemilatticeTest extends SemilatticeSpec("Boolean disjunction", BooleanOr)

class IntMaxIsMonoidTest extends MonoidSpec("Int maximum", IntMax)

class IntMaxIsSemilatticeTest extends SemilatticeSpec("Int maximum", IntMax)

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

/** The laws of [[Comonoid]], for comonoids in a monoidal structure on the category of a fixture. */
abstract class ComonoidSpec(
  name: String,
  tracked val F: Fixture,
  tracked val W: Comonoid { val V: Monoidal { val K: F.K.type } },
)(using
  S: Sample[W.C],
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?=> Sample[W.V.*[X, Y]],
  unit: Sample[W.V.I],
) extends LawSuite("Comonoid", name) {
  import W.ComonoidLaws.*
  import F.K.-->

  private given TensorSample: [X: Sample, Y: Sample] => Sample[W.V.*[X, Y]] = tensor[X, Y]

  law("leftCounit") {
    val observations = F.observe[W.C, W.V.*[W.V.I, W.C]]
    forAll(observations) { observe =>
      given ((W.C --> W.V.*[W.V.I, W.C]) is Observable) = observe
      leftCounit
    }
  }

  law("rightCounit") {
    val observations = F.observe[W.C, W.V.*[W.C, W.V.I]]
    forAll(observations) { observe =>
      given ((W.C --> W.V.*[W.C, W.V.I]) is Observable) = observe
      rightCounit
    }
  }

  law("coassociativity") {
    val observations = F.observe[W.C, W.V.*[W.C, W.V.*[W.C, W.C]]]
    forAll(observations) { observe =>
      given ((W.C --> W.V.*[W.C, W.V.*[W.C, W.C]]) is Observable) = observe
      coassociativity
    }
  }
}

class TotalProductComonoidTest extends ComonoidSpec("Int, by Δ and ! in 𝒮", TotalFixture, Total.Product.comonoid[Int])
class PartialProductComonoidTest
    extends ComonoidSpec("Int, by copying and deleting in 𝒫", PartialFixture, Partial.Product.comonoid[Int])
