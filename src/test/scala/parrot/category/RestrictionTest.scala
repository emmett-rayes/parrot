package parrot
package category

import org.scalacheck.Gen

import Sample.given

/** The laws of [[Restriction]]. */
abstract class RestrictionSpec(
  name: String,
  tracked val R: Restriction { val P: Promonad { val K: Category { type Obj = Type } } },
)(using
  PF: PromonadFixture.On[R.P.type],
  types: SampleTypes,
) extends LawSuite("Restriction", name) {
  import types.{T1, T2, T3, given}
  import PF.*
  import R.P
  import P.P
  import R.RestrictionLaws.*

  law("r1") {
    val observations = observe[T1, T2]
    val ps           = arrow[T1, T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T2] is Observable) = observe
      r1(p)
    }
  }

  law("r2") {
    val observations = observe[T1, T1]
    val ps           = arrow[T1, T2]
    val qs           = arrow[T1, T3]

    forAll(observations, ps, qs) { (observe, p, q) =>
      given (P[T1, T1] is Observable) = observe
      r2(p, q)
    }
  }

  law("r3") {
    val observations = observe[T1, T1]
    val ps           = arrow[T1, T2]
    val qs           = arrow[T1, T3]

    forAll(observations, ps, qs) { (observe, p, q) =>
      given (P[T1, T1] is Observable) = observe
      r3(p, q)
    }
  }

  law("r4") {
    val observations = observe[T1, T2]
    val ps           = arrow[T1, T2]
    val qs           = arrow[T2, T3]

    forAll(observations, ps, qs) { (observe, p, q) =>
      given (P[T1, T2] is Observable) = observe
      r4(p, q)
    }
  }

  law("pureTotal") {
    val observations = observe[T1, T1]
    val fs           = base.arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given (P[T1, T1] is Observable) = observe
      pureTotal(f)
    }
  }

  law("congruence") {
    val observations = observe[T1, T1]
    val ps           = arrow[T1, T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T1] is Observable) = observe
      congruence(p, variant(p))
    }
  }
}

/** The laws of [[Classical]], for classical structures over the coproducts of 𝒮. */
abstract class ClassicalSpec(
  name: String,
  tracked val C: Classical {
    val P: Promonad { val K: Category { type Obj = Type } }
    val C: Cocartesian { val T: Bifunctor { type Self = Either } }
  },
)(using
  PF: PromonadFixture.On[C.P.type],
  types: SampleTypes,
) extends LawSuite("Classical", name) {
  import types.{T1, T2, T3, given}
  import PF.*
  import C.P
  import P.P
  import C.ClassicalLaws.*

  law("zeroRestriction") {
    val observations = observe[T1, T1]

    forAll(observations) { observe =>
      given (P[T1, T1] is Observable) = observe
      zeroRestriction[T1, T2]
    }
  }

  law("zeroLeft") {
    val observations = observe[T1, T3]
    val ps           = arrow[T2, T3]

    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T3] is Observable) = observe
      zeroLeft[T1, T2, T3](p)
    }
  }

  law("zeroRight") {
    val observations = observe[T1, T3]
    val ps           = arrow[T1, T2]

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
      P.multiply(h, C.orElse(p, q)) =?= C.orElse(P.multiply(h, p), P.multiply(h, q))
    }
  }
}

/** 𝒫 at its total programs, as a promonad over itself. */
object PartialProgramsFixture extends PromonadFixture("Partial", Partial.Programs) {
  val base: PartialFixture.type = PartialFixture

  def arrow[X: Sample, Y: Sample]: Gen[X ~> Y] = PartialFixture.arrow[X, Y]

  def variant[X: Sample, Y: Sample](p: X ~> Y): X ~> Y = PartialFixture.variant(p)

  def observe[X: Sample, Y: Sample]: Gen[(X ~> Y) is Observable] = PartialFixture.observe[X, Y]
}

class OptionKleisliIsRestrictionTest
    extends RestrictionSpec("Kleisli[Option]", Kleisli.OptionDomains)

class OptionKleisliIsClassicalTest extends ClassicalSpec("Kleisli[Option]", Kleisli.OptionDomains)

class PartialIsRestrictionTest
    extends RestrictionSpec("Partial (total programs)", Partial.Domains)

class StringStateIsRestrictionTest
    extends RestrictionSpec("Kleisli[State[String, Option]]", StringStateDomains)

class StringStateIsClassicalTest
    extends ClassicalSpec("Kleisli[State[String, Option]]", StringStateDomains)

// ==== Failure over a writer: restrictions that keep the output ====

/** The writer of the maximum, a semilattice. */
object MaxWriter extends Writer(IntMax)

/** Computations that output a number, combined by maximum, and may fail. */
object MaxOutcome extends OptionT(MaxWriter)

/** The Kleisli arrows of [[MaxOutcome]]. */
object MaxOutcomeKleisli extends Kleisli(MaxOutcome)

/** Failure and choice for [[MaxOutcome]], keeping the output of what is tested. */
object MaxOutcomeClassical extends OptionT.ClassicalOf(MaxOutcome)

/** The restriction structure of [[MaxOutcomeKleisli]], keeping the output of what is tested. */
object MaxOutcomeDomains extends Kleisli.ClassicalOf(MaxOutcomeKleisli, MaxOutcomeClassical)

object MaxOutcomeFixture extends PromonadFixture("Kleisli[OptionT[Writer[max]]]", MaxOutcomeKleisli) {
  val base: TotalFixture.type = TotalFixture

  /** Arrows that output a small number, and fail or succeed. */
  def arrow[X: Sample, Y: Sample]: Gen[X -> (Int, Option[Y])] = {
    val results = Gen.zip(Gen.choose(-1, 3), Gen.frequency(1 -> Gen.const(None), 3 -> Y.gen.map(Some(_))))
    Gen.function1[X, (Int, Option[Y])](results)(using X.cogen)
  }

  def variant[X: Sample, Y: Sample](p: X -> (Int, Option[Y])): X -> (Int, Option[Y]) = {
    x => p(x)
  }

  def observe[X: Sample, Y: Sample]: Gen[(X -> (Int, Option[Y])) is Observable] = {
    TotalFixture.observe[X, (Int, Option[Y])]
  }
}

/** Keeping the output satisfies **R1**, **R3** and **R4**, but not **R2**: a failing test stops the output after it.
  * Nor the laws of zero and complement: 0 outputs nothing, while *p* ⨾ 0 and *p̄* ⨾ *p̄*ᶜ output what *p* does, and
  * *p̄* ⊳ *p̄*ᶜ outputs what *p* does where the identity outputs nothing.
  */
class MaxOutcomeRestrictionTest extends LawSuite("Restriction", "Kleisli[OptionT[Writer[max]]] (output kept)") {
  import MaxOutcomeDomains.RestrictionLaws.*
  import MaxOutcomeDomains.ClassicalLaws.*
  import MaxOutcomeFixture.{arrow, observe}

  law("r1") {
    val observations = observe[Int, String]
    val ps           = arrow[Int, String]

    forAll(observations, ps) { (o, p) =>
      given ((Int -> (Int, Option[String])) is Observable) = o
      r1(p)
    }
  }

  counterexample("r2", "a failing test stops the output after it") {
    val observations = observe[Int, Int]
    val ps           = arrow[Int, String]
    val qs           = arrow[Int, Boolean]

    forAll(observations, ps, qs) { (o, p, q) =>
      given ((Int -> (Int, Option[Int])) is Observable) = o
      r2(p, q)
    }
  }

  law("r3") {
    val observations = observe[Int, Int]
    val ps           = arrow[Int, String]
    val qs           = arrow[Int, Boolean]

    forAll(observations, ps, qs) { (o, p, q) =>
      given ((Int -> (Int, Option[Int])) is Observable) = o
      r3(p, q)
    }
  }

  law("r4") {
    val observations = observe[Int, String]
    val ps           = arrow[Int, String]
    val qs           = arrow[String, Boolean]

    forAll(observations, ps, qs) { (o, p, q) =>
      given ((Int -> (Int, Option[String])) is Observable) = o
      r4(p, q)
    }
  }

  also("Classical") {
    law("overridePrecomposition", "h runs twice; its output is idempotent") {
      val observations = observe[Int, Boolean]
      val hs           = arrow[Int, String]
      val ps           = arrow[String, Boolean]
      val qs           = arrow[String, Boolean]

      forAll(observations, hs, ps, qs) { (o, h, p, q) =>
        given ((Int -> (Int, Option[Boolean])) is Observable) = o
        overridePrecomposition(h, p, q)
      }
    }

    counterexample("zeroRight", "p ⨾ 0 keeps the output of p") {
      val observations = observe[Int, Boolean]
      val ps           = arrow[Int, String]

      forAll(observations, ps) { (o, p) =>
        given ((Int -> (Int, Option[Boolean])) is Observable) = o
        zeroRight[Int, String, Boolean](p)
      }
    }

    counterexample("complementExclusion", "the test outputs what p does") {
      val observations = observe[Int, Int]
      val ps           = arrow[Int, String]

      forAll(observations, ps) { (o, p) =>
        given ((Int -> (Int, Option[Int])) is Observable) = o
        complementExclusion(p)
      }
    }

    counterexample("complementCover", "the test outputs what p does") {
      val observations = observe[Int, Int]
      val ps           = arrow[Int, String]

      forAll(observations, ps) { (o, p) =>
        given ((Int -> (Int, Option[Int])) is Observable) = o
        complementCover(p)
      }
    }
  }
}

/** Failure over the writer of string concatenation, which is not a semilattice. */
object ConcatOutcome extends OptionT(StringWriter)

/** The Kleisli arrows of [[ConcatOutcome]]. */
object ConcatOutcomeKleisli extends Kleisli(ConcatOutcome)

/** Failure and choice for [[ConcatOutcome]], keeping the output of what is tested. */
object ConcatOutcomeClassical extends OptionT.ClassicalOf(ConcatOutcome)

/** The restriction structure of [[ConcatOutcomeKleisli]], keeping the output of what is tested. */
object ConcatOutcomeDomains extends Kleisli.ClassicalOf(ConcatOutcomeKleisli, ConcatOutcomeClassical)

/** Keeping an output that cannot be copied or reordered breaks the restriction laws, and backtracking repeats the
  * output of what came before the choice.
  */
class ConcatOutcomeIsNotRestrictionTest
    extends LawSuite("Restriction", "Kleisli[OptionT[Writer[String]]] (output kept)") {
  import ConcatOutcomeDomains.RestrictionLaws.*

  private def arrow[X: Sample, Y: Sample]: Gen[X -> (String, Option[Y])] = {
    val results = Gen.zip(Gen.oneOf("", "a", "b"), Gen.frequency(1 -> Gen.const(None), 3 -> Y.gen.map(Some(_))))
    Gen.function1[X, (String, Option[Y])](results)(using X.cogen)
  }

  counterexample("r1", "the output is not idempotent: p̄ ⨾ p outputs twice") {
    val observations = TotalFixture.observe[Int, (String, Option[String])]
    val ps           = arrow[Int, String]

    forAll(observations, ps) { (observe, p) =>
      given ((Int -> (String, Option[String])) is Observable) = observe
      r1(p)
    }
  }

  also("Classical") {
    counterexample("overridePrecomposition", "h runs twice, and outputs twice") {
      val observations = TotalFixture.observe[Int, (String, Option[Boolean])]
      val hs           = arrow[Int, String]
      val ps           = arrow[String, Boolean]

      forAll(observations, hs, ps) { (observe, h, p) =>
        given ((Int -> (String, Option[Boolean])) is Observable) = observe
        ConcatOutcomeDomains.ClassicalLaws.overridePrecomposition(h, p, p)
      }
    }
  }

  counterexample("r2", "the output is not commutative, and a failing test stops it") {
    val observations = TotalFixture.observe[Int, (String, Option[Int])]
    val ps           = arrow[Int, String]
    val qs           = arrow[Int, Boolean]

    forAll(observations, ps, qs) { (observe, p, q) =>
      given ((Int -> (String, Option[Int])) is Observable) = observe
      r2(p, q)
    }
  }
}

/** Override computes its second argument only where the first fails. */
class ClassicalMonadOrElseIsLazyTest extends org.scalatest.funsuite.AnyFunSuite {

  test("Option: the second argument is not computed where the first succeeds") {
    assert(ClassicalMonad.OptionIsClassical.orElse(Some(1), sys.error("computed")).contains(1))
  }

  test("State over Option: the second computation is not run where the first succeeds") {
    val first: String -> Option[(Int, String)] = s => Some((1, s))
    assert(StringStateClassical.orElse(first, sys.error("computed"))("x").contains((1, "x")))
  }
}
