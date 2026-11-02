package parrot
package category

import Category.Type

/** The laws of [[Comonoid]], for comonoids in a monoidal structure on a category whose objects are all types. */
abstract class ComonoidSpec(
  name: String,
  tracked val comonoid: Comonoid { val monoidal: Monoidal { val category: Category { type Obj = Type } } },
)(using
  category: CategoryFixture.On[comonoid.monoidal.category.type],
  S: Sample[comonoid.C],
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[comonoid.monoidal.*[X, Y]],
  unit: Sample[comonoid.monoidal.I],
) extends LawSuite("Comonoid", name) {
  import category.*
  import comonoid.C
  import comonoid.monoidal.{I, `*`}
  import comonoid.ComonoidLaws.*
  import comonoid.monoidal.category.-->

  private given TensorSample: [X: Sample, Y: Sample] => Sample[comonoid.monoidal.*[X, Y]] = tensor[X, Y]

  law("leftCounit") {
    val observations = observe[C, I * C]

    forAll(observations) { observe =>
      given ((C --> (I * C)) is Observable) = observe
      leftCounit
    }
  }

  law("rightCounit") {
    val observations = observe[C, C * I]

    forAll(observations) { observe =>
      given ((C --> (C * I)) is Observable) = observe
      rightCounit
    }
  }

  law("coassociativity") {
    val observations = observe[C, C * (C * C)]

    forAll(observations) { observe =>
      given ((C --> (C * (C * C))) is Observable) = observe
      coassociativity
    }
  }
}

class TotalProductComonoidTest extends ComonoidSpec("Int, by Δ and ! in 𝒮", Total.Products.comonoid[Int])
class PartialProductComonoidTest
    extends ComonoidSpec("Int, by copying and deleting in 𝒫", Partial.Product.comonoid[Int])
