package parrot
package category

/** The laws of [[Comonoid]], for comonoids in a monoidal structure on a category whose objects are all types. */
abstract class ComonoidSpec(
  name: String,
  tracked val W: Comonoid { val V: Monoidal { val K: Category { type Obj = Type } } },
)(using
  category: CategoryFixture.On[W.V.K.type],
  S: Sample[W.C],
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[W.V.*[X, Y]],
  unit: Sample[W.V.I],
) extends LawSuite("Comonoid", name) {
  import category.*
  import W.C
  import W.V.{I, `*`}
  import W.ComonoidLaws.*
  import W.V.K.-->

  private given TensorSample: [X: Sample, Y: Sample] => Sample[W.V.*[X, Y]] = tensor[X, Y]

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

class TotalProductComonoidTest extends ComonoidSpec("Int, by Δ and ! in 𝒮", Total.Product.comonoid[Int])
class PartialProductComonoidTest
    extends ComonoidSpec("Int, by copying and deleting in 𝒫", Partial.Product.comonoid[Int])
