package parrot
package category

/** The laws of [[Module]], for left actions on a category whose objects are all types. */
abstract class ModuleSpec(
  tracked val A: Module {
    val K: Category { type Obj = Type }
    val M: Monoidal { val K: Category { type Obj = Type } }
  },
)(using
  kCategory: CategoryFixture.On[A.K.type],
  mCategory: CategoryFixture.On[A.M.K.type],
  typename: TypeName[A.type],
  types: SampleTypes,
  action: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[A.Action[X, Y]],
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[A.M.Tensor[X, Y]],
  unit: Sample[A.M.I],
) extends LawSuite("Module", s"${typename.name} on ${kCategory.name}") {
  import types.{T1, T2, T3, T4, given}
  import kCategory.*
  import A.{Action as Act, ~}
  import A.K.-->
  import A.M.K.--> as ==>
  import A.M.`*`
  import A.ModuleLaws.*

  private given ActionSample: [X: Sample, Y: Sample] => Sample[A.Action[X, Y]]   = action[X, Y]
  private given TensorSample: [X: Sample, Y: Sample] => Sample[A.M.Tensor[X, Y]] = tensor[X, Y]

  law("leftUnitorIsomorphism") {
    val observations1 = observe[A.M.I ~ T1, A.M.I ~ T1]
    val observations2 = observe[T1, T1]

    forAll(observations1, observations2) { (o1, o2) =>
      given O1: (((A.M.I ~ T1) --> (A.M.I ~ T1)) is Observable) = o1
      given O2: ((T1 --> T1) is Observable)                     = o2
      leftUnitorIsomorphism[T1]
    }
  }

  law("associatorIsomorphism") {
    val observations1 = observe[(T1 * T2) ~ T4, (T1 * T2) ~ T4]
    val observations2 = observe[T1 ~ (T2 ~ T4), T1 ~ (T2 ~ T4)]

    forAll(observations1, observations2) { (o1, o2) =>
      given O1: ((((T1 * T2) ~ T4) --> ((T1 * T2) ~ T4)) is Observable) = o1
      given O2: (((T1 ~ (T2 ~ T4)) --> (T1 ~ (T2 ~ T4))) is Observable) = o2
      associatorIsomorphism[T1, T2, T4]
    }
  }

  law("leftUnitorNaturality") {
    val observations = observe[A.M.I ~ T1, T2]
    val fs           = arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given (((A.M.I ~ T1) --> T2) is Observable) = observe
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
    val observations = observe[(T1 * A.M.I) ~ T2, T1 ~ T2]

    forAll(observations) { observe =>
      given ((((T1 * A.M.I) ~ T2) --> (T1 ~ T2)) is Observable) = observe
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

object ProductSelfModule   extends Module.OfMonoidal(Total.Product)
object CoproductSelfModule extends Module.OfMonoidal(Total.Coproduct)

class ProductSelfModuleTest   extends ModuleSpec(ProductSelfModule)
class CoproductSelfModuleTest extends ModuleSpec(CoproductSelfModule)
