package parrot
package category

import org.scalacheck.Gen

import Sample.given
import Category.Type

/** The laws of [[Restriction]], with a functor *J* that picks out pure morphisms. */
abstract class RestrictionSpec(
  name: String,
  tracked val restriction: Restriction.On[Category { type Obj = Type }],
  tracked val functor: Functor.Into[restriction.category.type] {
    val source: Category { type Obj = Type }; type Self[A] = A
  },
  structure: String = "Restriction",
)(using
  category: CategoryFixture.For[restriction.category.type],
  source: CategoryFixture.For[functor.source.type],
  types: SampleTypes,
) extends LawSuite(structure, name) {
  import types.{T1, T2, T3, given}
  import category.*
  import restriction.category.-->
  import restriction.RestrictionLaws.*

  also("Restriction") {
    law("r1") {
      val observations = observe[T1, T2]
      val fs           = arrow[T1, T2]

      forAll(observations, fs) { (observe, f) =>
        given ((T1 --> T2) is Observable) = observe
        r1(f)
      }
    }

    law("r2") {
      val observations = observe[T1, T1]
      val fs           = arrow[T1, T2]
      val gs           = arrow[T1, T3]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((T1 --> T1) is Observable) = observe
        r2(f, g)
      }
    }

    law("r3") {
      val observations = observe[T1, T1]
      val fs           = arrow[T1, T2]
      val gs           = arrow[T1, T3]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((T1 --> T1) is Observable) = observe
        r3(f, g)
      }
    }

    law("r4") {
      val observations = observe[T1, T2]
      val fs           = arrow[T1, T2]
      val gs           = arrow[T2, T3]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((T1 --> T2) is Observable) = observe
        r4(f, g)
      }
    }

    law("pureTotal") {
      val observations = observe[T1, T1]
      val fs           = source.arrow[T1, T2]

      forAll(observations, fs) { (observe, f) =>
        given ((T1 --> T1) is Observable) = observe
        pureTotal(functor)(f)
      }
    }

    law("congruence") {
      val observations = observe[T1, T1]
      val fs           = arrow[T1, T2]

      forAll(observations, fs) { (observe, f) =>
        given ((T1 --> T1) is Observable) = observe
        congruence(f, variant(f))
      }
    }
  }
}

class PartialIsRestrictionTest extends RestrictionSpec("Partial", Partial.Domains, Partial.Inclusion)

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
  val category: TotalFixture.type = TotalFixture

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

    counterexample("zeroLeft", "0 ∘ p keeps the output of p") {
      val observations = observe[Int, Boolean]
      val ps           = arrow[Int, String]

      forAll(observations, ps) { (o, p) =>
        given ((Int -> (Int, Option[Boolean])) is Observable) = o
        zeroLeft[Int, String, Boolean](p)
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
    assert(Monad.Classical.OptionIsClassical.orElse(Some(1), sys.error("computed")).contains(1))
  }

  test("State over Option: the second computation is not run where the first succeeds") {
    val first: String -> Option[(Int, String)] = s => Some((1, s))
    assert(StringStateClassical.orElse(first, sys.error("computed"))("x").contains((1, "x")))
  }
}
