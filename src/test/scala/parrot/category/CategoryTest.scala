package parrot
package category

/** The laws of [[Category]], for a category whose objects are all types. */
abstract class CategorySpec(tracked val K: Category { type Obj = Type })(
  using
  F: CategoryFixture.On[K.type],
  types: SampleTypes,
) extends LawSuite("Category", F.name) {
  import types.{T1, T2, T3, T4, given}
  import F.*
  import K.-->
  import K.CategoryLaws.*

  law("leftIdentity") {
    val observations = observe[T1, T2]
    val fs           = arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given ((T1 --> T2) is Observable) = observe
      leftIdentity(f)
    }
  }

  law("rightIdentity") {
    val observations = observe[T1, T2]
    val fs           = arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given ((T1 --> T2) is Observable) = observe
      rightIdentity(f)
    }
  }

  law("associativity") {
    val observations = observe[T1, T4]
    val fs           = arrow[T1, T2]
    val gs           = arrow[T2, T3]
    val hs           = arrow[T3, T4]

    forAll(observations, fs, gs, hs) { (observe, f, g, h) =>
      given ((T1 --> T4) is Observable) = observe
      associativity(f, g, h)
    }
  }

  law("congruence") {
    val observations = observe[T1, T3]
    val fs           = arrow[T1, T2]
    val gs           = arrow[T2, T3]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given ((T1 --> T3) is Observable) = observe
      congruence(f, variant(f), g, variant(g))
    }
  }
}

class TotalIsCategoryTest         extends CategorySpec(Total)
class ScalaOpIsCategoryTest       extends CategorySpec(Total.op)
class PartialIsCategoryTest       extends CategorySpec(Partial)
class OptionKleisliIsCategoryTest extends CategorySpec(Kleisli.OptionKleisli.category)
