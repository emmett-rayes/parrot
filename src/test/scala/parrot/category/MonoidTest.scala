package parrot
package category

import Sample.given
import Category.Type

/** Strings under concatenation: a monoid in 𝒮 that is neither commutative nor idempotent. */
object StringConcat extends Monoid(Total.Products) {
  type Self = String

  def evidence: String is Type = Type.TIsType

  def unit: Unit -> String = {
    _ => ""
  }

  def multiply: ((String, String)) -> String = {
    (a, b) => a + b
  }
}

/** The laws of [[Monoid]], for monoids in a monoidal structure on a category whose objects are all types. */
abstract class MonoidSpec(
  name: String,
  tracked val monoid: Monoid.In[Monoidal.On[Category { type Obj = Type }]],
  structure: String = "Monoid",
)(using
  category: CategoryFixture.For[monoid.monoidal.category.type],
  S: Sample[monoid.M],
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[monoid.monoidal.*[X, Y]],
  unit: Sample[monoid.monoidal.I],
) extends LawSuite(structure, name) {
  import category.*
  import monoid.M
  import monoid.monoidal.{I, `*`}
  import monoid.MonoidLaws.*
  import monoid.monoidal.category.-->

  private given TensorSample: [X: Sample, Y: Sample] => Sample[monoid.monoidal.*[X, Y]] = tensor[X, Y]

  also("Monoid") {
    law("leftUnit") {
      val observations = observe[I * M, M]

      forAll(observations) { observe =>
        given (((I * M) --> M) is Observable) = observe
        leftUnit
      }
    }

    law("rightUnit") {
      val observations = observe[M * I, M]

      forAll(observations) { observe =>
        given (((M * I) --> M) is Observable) = observe
        rightUnit
      }
    }

    law("associativity") {
      val observations = observe[(M * M) * M, M]

      forAll(observations) { observe =>
        given ((((M * M) * M) --> M) is Observable) = observe
        associativity
      }
    }
  }
}

class StringConcatIsMonoidTest extends MonoidSpec("String concatenation", StringConcat)
class TotalCoproductMonoidTest extends MonoidSpec("Int, by ∇ and ¡ in 𝒮", Total.Coproducts.monoid[Int])
