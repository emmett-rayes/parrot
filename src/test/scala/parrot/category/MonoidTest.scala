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

/** The laws of [[Monoid]] for monoids in 𝒮 with pairs. */
abstract class MonoidSpec(name: String, tracked val W: Monoid { val V: Total.Product.type })(
  using S: Sample[W.M]
) extends LawSuite("Monoid", name) {
  import W.M
  import W.V.{I, `*`}
  import W.MonoidLaws.*

  law("leftUnit") {
    val observations = TotalFixture.observe[I * M, M]

    forAll(observations) { observe =>
      given (((I * M) -> M) is Observable) = observe
      leftUnit
    }
  }

  law("rightUnit") {
    val observations = TotalFixture.observe[M * I, M]

    forAll(observations) { observe =>
      given (((M * I) -> M) is Observable) = observe
      rightUnit
    }
  }

  law("associativity") {
    val observations = TotalFixture.observe[(M * M) * M, M]

    forAll(observations) { observe =>
      given ((((M * M) * M) -> M) is Observable) = observe
      associativity
    }
  }
}

class StringConcatIsMonoidTest extends MonoidSpec("String concatenation", StringConcat)

class BooleanOrIsMonoidTest extends MonoidSpec("Boolean disjunction", BooleanOr)

class IntMaxIsMonoidTest extends MonoidSpec("Int maximum", IntMax)
