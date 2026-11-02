package parrot
package category

import Category.Type

/** The laws of [[Module]], for left actions on a category whose objects are all types. */
abstract class ModuleSpec(
  tracked val module: Module {
    val category: Category { type Obj = Type }
    val monoidal: Monoidal { val category: Category { type Obj = Type } }
  },
)(using
  kCategory: CategoryFixture.On[module.category.type],
  mCategory: CategoryFixture.On[module.monoidal.category.type],
  typename: TypeName[module.type],
  types: SampleTypes,
  action: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[module.Action[X, Y]],
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[module.monoidal.Tensor[X, Y]],
  unit: Sample[module.monoidal.I],
) extends LawSuite("Module", s"${typename.name} on ${kCategory.name}") {
  import types.{T1, T2, T3, T4, given}
  import kCategory.*
  import module.{Action as Act, ~}
  import module.category.-->
  import module.monoidal.category.--> as ==>
  import module.monoidal.`*`
  import module.ModuleLaws.*

  private given ActionSample: [X: Sample, Y: Sample] => Sample[module.Action[X, Y]]          = action[X, Y]
  private given TensorSample: [X: Sample, Y: Sample] => Sample[module.monoidal.Tensor[X, Y]] = tensor[X, Y]

  law("leftUnitorLeftInverse") {
    val observations = observe[module.monoidal.I ~ T1, module.monoidal.I ~ T1]

    forAll(observations) { observe =>
      given (((module.monoidal.I ~ T1) --> (module.monoidal.I ~ T1)) is Observable) = observe
      leftUnitorLeftInverse[T1]
    }
  }

  law("leftUnitorRightInverse") {
    val observations = observe[T1, T1]

    forAll(observations) { observe =>
      given ((T1 --> T1) is Observable) = observe
      leftUnitorRightInverse[T1]
    }
  }

  law("associatorLeftInverse") {
    val observations = observe[(T1 * T2) ~ T4, (T1 * T2) ~ T4]

    forAll(observations) { observe =>
      given ((((T1 * T2) ~ T4) --> ((T1 * T2) ~ T4)) is Observable) = observe
      associatorLeftInverse[T1, T2, T4]
    }
  }

  law("associatorRightInverse") {
    val observations = observe[T1 ~ (T2 ~ T4), T1 ~ (T2 ~ T4)]

    forAll(observations) { observe =>
      given (((T1 ~ (T2 ~ T4)) --> (T1 ~ (T2 ~ T4))) is Observable) = observe
      associatorRightInverse[T1, T2, T4]
    }
  }

  law("leftUnitorNaturality") {
    val observations = observe[module.monoidal.I ~ T1, T2]
    val fs           = arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given (((module.monoidal.I ~ T1) --> T2) is Observable) = observe
      leftUnitorNaturality(f)
    }
  }

  law("associatorNaturality") {
    val observations = observe[(T1 * T3) ~ T2, T4 ~ (T2 ~ T3)]
    val gs           = mCategory.arrow[T1, T4]
    val hs           = mCategory.arrow[T3, T2]
    val fs           = arrow[T2, T3]

    forAll(observations, gs, hs, fs) { (observe, g, h, f) =>
      given ((((T1 * T3) ~ T2) --> (T4 ~ (T2 ~ T3))) is Observable) = observe
      associatorNaturality(g, h, f)
    }
  }

  law("triangle") {
    val observations = observe[(T1 * module.monoidal.I) ~ T2, T1 ~ T2]

    forAll(observations) { observe =>
      given ((((T1 * module.monoidal.I) ~ T2) --> (T1 ~ T2)) is Observable) = observe
      triangle[T1, T2]
    }
  }

  law("pentagon") {
    val observations = observe[(((T1 * T2) * T3) ~ T4), T1 ~ (T2 ~ (T3 ~ T4))]

    forAll(observations) { observe =>
      given (((((T1 * T2) * T3) ~ T4) --> (T1 ~ (T2 ~ (T3 ~ T4)))) is Observable) = observe
      pentagon[T1, T2, T3, T4]
    }
  }
}

object ProductSelfModule   extends Module.OfMonoidal(Total.Products)
object CoproductSelfModule extends Module.OfMonoidal(Total.Coproducts)

class ProductSelfModuleTest   extends ModuleSpec(ProductSelfModule)
class CoproductSelfModuleTest extends ModuleSpec(CoproductSelfModule)
