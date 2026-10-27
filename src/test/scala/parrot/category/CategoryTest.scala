package parrot
package category

/** The laws of [[Category]], for a category whose objects are all types. */
abstract class CategorySpec(tracked val F: Fixture)(using types: SampleTypes) extends LawSuite("Category", F.name) {
  import types.{T1, T2, T3, T4, given}
  import F.K.CategoryLaws.*
  import F.K.-->

  law("leftIdentity") {
    val observations = F.observe[T1, T2]
    val fs           = F.arrow[T1, T2]
    forAll(observations, fs) { (observe, f) =>
      given ((T1 --> T2) is Observable) = observe
      leftIdentity(f)
    }
  }

  law("rightIdentity") {
    val observations = F.observe[T1, T2]
    val fs           = F.arrow[T1, T2]
    forAll(observations, fs) { (observe, f) =>
      given ((T1 --> T2) is Observable) = observe
      rightIdentity(f)
    }
  }

  law("associativity") {
    val observations = F.observe[T1, T4]
    val fs           = F.arrow[T1, T2]
    val gs           = F.arrow[T2, T3]
    val hs           = F.arrow[T3, T4]
    forAll(observations, fs, gs, hs) { (observe, f, g, h) =>
      given ((T1 --> T4) is Observable) = observe
      associativity(f, g, h)
    }
  }

  law("congruence") {
    val observations = F.observe[T1, T3]
    val fs           = F.arrow[T1, T2]
    val gs           = F.arrow[T2, T3]
    forAll(observations, fs, gs) { (observe, f, g) =>
      given ((T1 --> T3) is Observable) = observe
      congruence(f, F.variant(f), g, F.variant(g))
    }
  }
}

class TotalIsCategoryTest extends CategorySpec(TotalFixture)
class ScalaOpIsCategoryTest extends CategorySpec(OpFixture(TotalFixture))
class PartialIsCategoryTest extends CategorySpec(PartialFixture)
class OptionKleisliIsCategoryTest extends CategorySpec(OptionKleisliFixture.category)
