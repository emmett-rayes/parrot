package parrot
package category

import org.scalacheck.Gen

import Sample.given
import Category.Type

/** The laws of [[Classical]], for classical structures over the coproducts of 𝒮. */
abstract class ClassicalSpec(
  name: String,
  tracked override val restriction: Classical.On[Promonad.On[Category { type Obj = Type }]] {
    val cocartesian: Cocartesian { val tensor: Bifunctor { type Self = Either } }
  },
)(using
  promonad: PromonadFixture.For[restriction.promonad.type],
  types: SampleTypes,
) extends RestrictionSpec(name, restriction, "Classical") {
  import types.{T1, T2, T3, given}
  import promonad.*
  import restriction.promonad.{P, >>>}
  import restriction.ClassicalLaws.*

  law("zeroRestriction") {
    val observations = observe[T1, T1]

    forAll(observations) { observe =>
      given (P[T1, T1] is Observable) = observe
      zeroRestriction[T1, T2]
    }
  }

  law("zeroLeft") {
    val observations = observe[T1, T3]
    val ps           = arrow[T1, T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T3] is Observable) = observe
      zeroLeft[T1, T2, T3](p)
    }
  }

  law("zeroRight") {
    val observations = observe[T1, T3]
    val ps           = arrow[T2, T3]

    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T3] is Observable) = observe
      zeroRight[T1, T2, T3](p)
    }
  }

  law("overrideZero") {
    val observations = observe[T1, T2]
    val ps           = arrow[T1, T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T2] is Observable) = observe
      overrideZero(p)
    }
  }

  law("overrideAssociativity") {
    val observations = observe[T1, T2]
    val ps           = arrow[T1, T2]
    val qs           = arrow[T1, T2]
    val rs           = arrow[T1, T2]

    forAll(observations, ps, qs, rs) { (observe, p, q, r) =>
      given (P[T1, T2] is Observable) = observe
      overrideAssociativity(p, q, r)
    }
  }

  law("overrideRestricted") {
    val observations = observe[T1, T2]
    val ps           = arrow[T1, T2]
    val qs           = arrow[T1, T2]

    forAll(observations, ps, qs) { (observe, p, q) =>
      given (P[T1, T2] is Observable) = observe
      overrideRestricted(p, q)
    }
  }

  law("overrideRestricting") {
    val observations = observe[T1, T2]
    val ps           = arrow[T1, T2]
    val qs           = arrow[T1, T3]

    forAll(observations, ps, qs) { (observe, p, q) =>
      given (P[T1, T2] is Observable) = observe
      overrideRestricting(p, q)
    }
  }

  law("overridePrecomposition") {
    val observations = observe[T1, T3]
    val hs           = arrow[T1, T2]
    val ps           = arrow[T2, T3]
    val qs           = arrow[T2, T3]

    forAll(observations, hs, ps, qs) { (observe, h, p, q) =>
      given (P[T1, T3] is Observable) = observe
      overridePrecomposition(h, p, q)
    }
  }

  law("overrideRestriction") {
    val observations = observe[T1, T3]
    val ps           = arrow[T1, T2]
    val qs           = arrow[T1, T2]
    val hs           = arrow[T1, T3]

    forAll(observations, ps, qs, hs) { (observe, p, q, h) =>
      given (P[T1, T3] is Observable) = observe
      overrideRestriction(p, q, h)
    }
  }

  law("complementExclusion") {
    val observations = observe[T1, T1]
    val ps           = arrow[T1, T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T1] is Observable) = observe
      complementExclusion(p)
    }
  }

  law("complementCover") {
    val observations = observe[T1, T1]
    val ps           = arrow[T1, T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T1] is Observable) = observe
      complementCover(p)
    }
  }

  law("complementRestriction") {
    val observations = observe[T1, T1]
    val ps           = arrow[T1, T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T1] is Observable) = observe
      complementRestriction(p)
    }
  }

  law("doubleComplement") {
    val observations = observe[T1, T1]
    val ps           = arrow[T1, T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T1] is Observable) = observe
      doubleComplement(p)
    }
  }

  law("attemptDefinition") {
    val observations = observe[T1, Either[T2, T1]]
    val ps           = arrow[T1, T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T1, Either[T2, T1]] is Observable) = observe
      attemptDefinition(p)
    }
  }

  law("congruence") {
    val ps = arrow[T1, T2]
    val qs = arrow[T1, T2]

    forAll(Gen.zip(observe[T1, T2], observe[T1, T1]), ps, qs) { case ((o1, o2), p, q) =>
      given O1: (P[T1, T2] is Observable) = o1
      given O2: (P[T1, T1] is Observable)    = o2
      congruence(p, variant(p), q, variant(q))
    }
  }

  counterexample("overridePostcomposition", "(p ⊳ q) ⨾ h = (p ⨾ h) ⊳ (q ⨾ h) fails: ⊳ commits") {
    val observations = observe[T1, T3]
    val ps           = arrow[T1, T2]
    val qs           = arrow[T1, T2]
    val hs           = arrow[T2, T3]

    forAll(observations, ps, qs, hs) { (observe, p, q, h) =>
      given (P[T1, T3] is Observable) = observe
      (restriction.orElse(p, q) >>> h) =?= restriction.orElse(p >>> h, q >>> h)
    }
  }
}

class OptionKleisliIsClassicalTest extends ClassicalSpec("Kleisli[Option]", Kleisli.OptionDomains)

class StringStateIsClassicalTest
    extends ClassicalSpec("Kleisli[State[String, Option]]", StringStateDomains)
