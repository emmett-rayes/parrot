package parrot
package category

import org.scalacheck.Gen

import Sample.given
import Category.Type

/** The laws of [[Recursion]], with functions that recurse on smaller arguments (𝒫) or after progress (guarded). */
abstract class RecursionSpec(
  name: String,
  tracked val recursion: Recursion { val promonad: Promonad { val category: Category { type Obj = Type } } },
)(using
  val promonad: PromonadFixture.On[recursion.promonad.type],
  types: SampleTypes,
) extends LawSuite("Recursion", name) {
  import types.{T2, given}
  import promonad.*
  import recursion.promonad.P
  import recursion.RecursionLaws.*

  /** Functions from arrows to arrows whose fixed point is defined. */
  def guarded[B: Sample]: Gen[P[Int, B] -> P[Int, B]]

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
}

// ==== 𝒫 ====

class PartialKnotsIsRecursionTest extends RecursionSpec("Partial (knots)", Partial.Knots) {
  def guarded[B: Sample]: Gen[(Int ~> B) -> (Int ~> B)] = {
    for {
      base    <- Sample.function[Int, B]
      go      <- Sample.function[Int, Boolean]
      k       <- Sample.function[Int, Int]
      combine <- Sample.function[(Int, B), B]
    } yield (rec: Int ~> B) =>
      Partial(x => if x == 0 || !go(x) then base(x) else combine((x, rec.run(Descent.below(x, k(x))))))
  }
}

// ==== Guarded state ====

class StringStateRecursionIsRecursionTest
    extends RecursionSpec("Kleisli[State[String, Option]] (guarded)", StringStateRecursion) {
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

  counterexample("fixedPoint", "for left-recursive functions") {
    val observations = StringStateFixture.observe[Int, String]
    val bases        = StringStateFixture.arrow[Int, String]

    forAll(observations, bases) { (observe, base) =>
      given ((Int -> String -> Option[(String, String)]) is Observable) = observe
      val leftRecursive: (Int -> String -> Option[(String, String)]) -> Int -> String -> Option[(String, String)] = {
        rec => x => s => rec(x)(s).map((b, s2) => (b + "!", s2)).orElse(base(x)(s))
      }
      StringStateRecursion.RecursionLaws.fixedPoint(leftRecursive)
    }
  }
}
