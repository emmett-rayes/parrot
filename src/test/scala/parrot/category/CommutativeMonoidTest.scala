package parrot
package category

import Sample.given
import Category.Type

/** The laws of [[CommutativeMonoid]], for monoids in a symmetric monoidal structure on a category whose objects are all
  * types.
  */
abstract class CommutativeMonoidSpec(
  name: String,
  tracked override val monoid: CommutativeMonoid.In[Symmetric.On[Category { type Obj = Type }]],
  structure: String = "CommutativeMonoid",
)(using
  category: CategoryFixture.For[monoid.monoidal.category.type],
  S: Sample[monoid.M],
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[monoid.monoidal.*[X, Y]],
  unit: Sample[monoid.monoidal.I],
) extends MonoidSpec(name, monoid, structure) {
  import category.*
  import monoid.M
  import monoid.monoidal.`*`
  import monoid.CommutativeMonoidLaws.*
  import monoid.monoidal.category.-->

  private given TensorSample: [X: Sample, Y: Sample] => Sample[monoid.monoidal.*[X, Y]] = tensor[X, Y]

  also("CommutativeMonoid") {
    law("commutativity") {
      val observations = observe[M * M, M]

      forAll(observations) { observe =>
        given (((M * M) --> M) is Observable) = observe
        commutativity
      }
    }
  }
}

/** Integers under addition: a commutative monoid in 𝒮 that is not idempotent. */
object IntSum extends CommutativeMonoid(Total.Products) {
  type Self = Int

  def evidence: Int is Type = Type.TIsType

  def unit: Unit -> Int = {
    _ => 0
  }

  def multiply: ((Int, Int)) -> Int = {
    (a, b) => a + b
  }
}

class IntSumIsCommutativeMonoidTest extends CommutativeMonoidSpec("Int addition", IntSum)
