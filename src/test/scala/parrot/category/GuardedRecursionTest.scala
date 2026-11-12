package parrot
package category

import org.scalacheck.Gen

import Sample.given
import Category.Type

/** The laws of [[GuardedRecursion]], with guarded functions: functions that call their argument after progress. */
abstract class GuardedRecursionSpec(
  name: String,
  tracked val recursion: GuardedRecursion.On[Promonad.On[Category { type Obj = Type }]],
  structure: String = "GuardedRecursion",
)(using
  val promonad: PromonadFixture.For[recursion.promonad.type],
  types: SampleTypes,
) extends LawSuite(structure, name) {
  import types.{T2, given}
  import promonad.*
  import recursion.promonad.P
  import recursion.GuardedRecursionLaws.*

  /** Guarded functions from arrows to arrows. */
  def guarded[B: Sample]: Gen[P[Int, B] -> P[Int, B]]

  also("GuardedRecursion") {
    law("fixedPoint") {
      val observations = observe[Int, T2]
      val fs           = guarded[T2]

      forAll(observations, fs) { (observe, f) =>
        given (P[Int, T2] is Observable) = observe
        fixedPoint(f)
      }
    }

    law("familyFixedPoint", "two arrows, each calling the other") {
      val observations = observe[Int, T2]
      val g0s          = guarded[T2]
      val g1s          = guarded[T2]

      forAll(observations, g0s, g1s) { (observe, g0, g1) =>
        given (P[Int, T2] is Observable) = observe
        familyFixedPoint[Int, T2](2)(rec => i => if i == 0 then g0(rec(1)) else g1(rec(0)))
      }
    }

    law("fixFamilyIsBekic", "two arrows, each calling the other") {
      val observations = observe[Int, T2]
      val g0s          = guarded[T2]
      val g1s          = guarded[T2]

      forAll(observations, g0s, g1s) { (observe, g0, g1) =>
        given (P[Int, T2] is Observable) = observe
        fixFamilyIsBekic[Int, T2](2)(rec => i => if i == 0 then g0(rec(1)) else g1(rec(0)))
      }
    }
  }
}

// ==== Guarded state ====

class StringStateRecursionIsGuardedRecursionTest
    extends GuardedRecursionSpec("Kleisli[State[String, Option]] (guarded)", StringStateRecursion) {
  def guarded[B: Sample]: Gen[(Int -> String -> Option[(B, String)]) -> Int -> String -> Option[(B, String)]] = {
    for {
      base    <- StringStateFixture.arrow[Int, B]
      go      <- Sample.function[(Int, String), Boolean]
      combine <- Sample.function[(Int, B), B]
    } yield rec =>
      x =>
        s =>
          if s.isEmpty || !go((x, s)) then base(x)(s)
          else rec(x / 2)(s.tail).map((b, s2) => (combine((x, b)), s2)).orElse(base(x)(s))
  }

  also("Recursion") {
    counterexample("fixedPoint", "for left-recursive functions") {
      val observations = StringStateFixture.observe[Int, String]
      val bases        = StringStateFixture.arrow[Int, String]

      forAll(observations, bases) { (observe, base) =>
        given ((Int -> String -> Option[(String, String)]) is Observable) = observe
        val leftRecursive: (Int -> String -> Option[(String, String)]) -> Int -> String -> Option[(String, String)] = {
          rec => x => s => rec(x)(s).map((b, s2) => (b + "!", s2)).orElse(base(x)(s))
        }
        StringStateRecursion.GuardedRecursionLaws.fixedPoint(leftRecursive)
      }
    }

    counterexample("fixFamilyIsBekic", "for left-recursive families") {
      val observations = StringStateFixture.observe[Int, String]
      val bases        = StringStateFixture.arrow[Int, String]

      forAll(observations, bases) { (observe, base) =>
        given ((Int -> String -> Option[(String, String)]) is Observable) = observe
        val leftRecursive
          : (Int -> Int -> String -> Option[(String, String)]) -> Int -> Int -> String -> Option[(String, String)] = {
          rec =>
            i =>
              x =>
                s =>
                  if i == 0 then rec(1)(x)(s)
                  else rec(0)(x)(s).map((b, s2) => (b + "!", s2)).orElse(base(x)(s))
        }
        StringStateRecursion.GuardedRecursionLaws.fixFamilyIsBekic(2)(leftRecursive)
      }
    }
  }
}
