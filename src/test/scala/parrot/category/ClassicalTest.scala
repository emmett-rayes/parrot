package parrot
package category

import org.scalacheck.Gen

import Sample.given
import Category.Type

/** The laws of [[Classical]], with a functor *J* that picks out pure morphisms. */
abstract class ClassicalSpec(
  name: String,
  tracked override val restriction: Classical.On[Category { type Obj = Type }],
  tracked override val functor: Functor.Into[restriction.category.type] {
    val source: Category { type Obj = Type }; type Self[A] = A
  },
)(using
  category: CategoryFixture.For[restriction.category.type],
  source: CategoryFixture.For[functor.source.type],
  types: SampleTypes,
) extends RestrictionSpec(name, restriction, functor, "Classical") {
  import types.{T1, T2, T3, given}
  import category.*
  import restriction.category.{-->, >>>}
  import restriction.ClassicalLaws.*

  law("zeroRestriction") {
    val observations = observe[T1, T1]

    forAll(observations) { observe =>
      given ((T1 --> T1) is Observable) = observe
      zeroRestriction[T1, T2]
    }
  }

  law("zeroLeft") {
    val observations = observe[T1, T3]
    val fs           = arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given ((T1 --> T3) is Observable) = observe
      zeroLeft[T1, T2, T3](f)
    }
  }

  law("zeroRight") {
    val observations = observe[T1, T3]
    val fs           = arrow[T2, T3]

    forAll(observations, fs) { (observe, f) =>
      given ((T1 --> T3) is Observable) = observe
      zeroRight[T1, T2, T3](f)
    }
  }

  law("overrideZero") {
    val observations = observe[T1, T2]
    val fs           = arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given ((T1 --> T2) is Observable) = observe
      overrideZero(f)
    }
  }

  law("overrideAssociativity") {
    val observations = observe[T1, T2]
    val fs           = arrow[T1, T2]
    val gs           = arrow[T1, T2]
    val hs           = arrow[T1, T2]

    forAll(observations, fs, gs, hs) { (observe, f, g, h) =>
      given ((T1 --> T2) is Observable) = observe
      overrideAssociativity(f, g, h)
    }
  }

  law("overrideRestricted") {
    val observations = observe[T1, T2]
    val fs           = arrow[T1, T2]
    val gs           = arrow[T1, T2]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given ((T1 --> T2) is Observable) = observe
      overrideRestricted(f, g)
    }
  }

  law("overrideRestricting") {
    val observations = observe[T1, T2]
    val fs           = arrow[T1, T2]
    val gs           = arrow[T1, T3]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given ((T1 --> T2) is Observable) = observe
      overrideRestricting(f, g)
    }
  }

  law("overridePrecomposition") {
    val observations = observe[T1, T3]
    val hs           = arrow[T1, T2]
    val fs           = arrow[T2, T3]
    val gs           = arrow[T2, T3]

    forAll(observations, hs, fs, gs) { (observe, h, f, g) =>
      given ((T1 --> T3) is Observable) = observe
      overridePrecomposition(h, f, g)
    }
  }

  law("overrideRestriction") {
    val observations = observe[T1, T3]
    val fs           = arrow[T1, T2]
    val gs           = arrow[T1, T2]
    val hs           = arrow[T1, T3]

    forAll(observations, fs, gs, hs) { (observe, f, g, h) =>
      given ((T1 --> T3) is Observable) = observe
      overrideRestriction(f, g, h)
    }
  }

  law("complementExclusion") {
    val observations = observe[T1, T1]
    val fs           = arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given ((T1 --> T1) is Observable) = observe
      complementExclusion(f)
    }
  }

  law("complementCover") {
    val observations = observe[T1, T1]
    val fs           = arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given ((T1 --> T1) is Observable) = observe
      complementCover(f)
    }
  }

  law("complementRestriction") {
    val observations = observe[T1, T1]
    val fs           = arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given ((T1 --> T1) is Observable) = observe
      complementRestriction(f)
    }
  }

  law("doubleComplement") {
    val observations = observe[T1, T1]
    val fs           = arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given ((T1 --> T1) is Observable) = observe
      doubleComplement(f)
    }
  }

  law("congruence") {
    val fs = arrow[T1, T2]
    val gs = arrow[T1, T2]

    forAll(Gen.zip(observe[T1, T2], observe[T1, T1]), fs, gs) { case ((o1, o2), f, g) =>
      given O1: ((T1 --> T2) is Observable) = o1
      given O2: ((T1 --> T1) is Observable) = o2
      congruence(f, variant(f), g, variant(g))
    }
  }

  counterexample("overridePostcomposition", "h ∘ (f ⊳ g) = (h ∘ f) ⊳ (h ∘ g) fails: ⊳ commits") {
    val observations = observe[T1, T3]
    val fs           = arrow[T1, T2]
    val gs           = arrow[T1, T2]
    val hs           = arrow[T2, T3]

    forAll(observations, fs, gs, hs) { (observe, f, g, h) =>
      given ((T1 --> T3) is Observable) = observe
      (restriction.orElse(f, g) >>> h) =?= restriction.orElse(f >>> h, g >>> h)
    }
  }
}

class OptionKleisliIsClassicalTest
    extends ClassicalSpec("Kleisli[Option]", Kleisli.OptionDomains, Kleisli.OptionKleisli.pure)

class StringStateIsClassicalTest
    extends ClassicalSpec("Kleisli[State[String, Option]]", StringStateDomains, StringStateKleisli.pure)
