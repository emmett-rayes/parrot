package parrot
package category

import org.scalacheck.Gen

import Sample.given
import Category.Type

/** The laws of [[GuardedIteration]], with guarded steps: steps that make progress whenever they continue. */
abstract class GuardedIterationSpec(
  name: String,
  tracked val iteration: GuardedIteration.On[Bistrong.On[Promonad.On[Category { type Obj = Type }]]],
  structure: String = "GuardedIteration",
)(using
  val promonad: PromonadFixture.For[iteration.strong.profunctor.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[iteration.strong.monoidal.Tensor[X, Y]],
) extends LawSuite(structure, name) {
  import types.{T2, T3, given}
  import promonad.*
  import iteration.strong.profunctor
  import profunctor.{P, >>>}
  import iteration.GuardedIterationLaws.*
  import profunctor.category.-->

  private given TensorSample: [X: Sample, Y: Sample] => Sample[iteration.strong.monoidal.Tensor[X, Y]] = tensor[X, Y]

  /** Guarded steps. */
  def step[A: Sample]: Gen[P[Int, iteration.strong.monoidal.Tensor[A, Int]]]

  /** Steps with two ways to continue, for the double dagger law. */
  def step2[A: Sample]: Gen[P[Int, iteration.strong.monoidal.Tensor[iteration.strong.monoidal.Tensor[A, Int], Int]]]

  /** A pure map that keeps loops stopping: it does not move a state away from 0. */
  def shrink: Int --> Int

  /** A pure bijection that keeps loops stopping, with its inverse. */
  def bijection: (Int --> Int, Int --> Int)

  also("GuardedIteration") {
    law("fixedPoint") {
      val observations = observe[Int, T2]
      val ps           = step[T2]

      forAll(observations, ps) { (observe, p) =>
        given (P[Int, T2] is Observable) = observe
        fixedPoint(p)
      }
    }

    law("parameterNaturality") {
      val observations = observe[Int, T3]
      val ps           = step[T2]
      val hs           = category.arrow[T2, T3]

      forAll(observations, ps, hs) { (observe, p, h) =>
        given (P[Int, T3] is Observable) = observe
        parameterNaturality(p, h)
      }
    }

    law("composition") {
      val observations = observe[Int, T2]
      val ps           = step[T2]

      forAll(observations, ps) { (observe, p) =>
        given (P[Int, T2] is Observable) = observe
        composition[T2, Int, Int](p, shrink)
      }
    }

    law("dinaturality") {
      val observations = observe[Int, T2]
      val fs           = step[T2]
      val gs           = step[T2]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given (P[Int, T2] is Observable) = observe
        dinaturality[T2, Int, Int](f, g)
      }
    }

    law("doubleDagger") {
      val observations = observe[Int, T2]
      val ps           = step2[T2]

      forAll(observations, ps) { (observe, p) =>
        given (P[Int, T2] is Observable) = observe
        doubleDagger(p)
      }
    }

    law("uniformity") {
      val observations = observe[Int, T2]
      val fs           = step[T2]

      forAll(observations, fs) { (observe, f) =>
        given (P[Int, T2] is Observable) = observe
        val (h, inverse)                          = bijection
        val g = profunctor.unit(inverse) >>> f >>> iteration.strong.left[Int, Int, T2](profunctor.unit(h))
        uniformity(f, g, h)
      }
    }

    law("congruence") {
      val observations = observe[Int, T2]
      val ps           = step[T2]

      forAll(observations, ps) { (observe, p) =>
        given (P[Int, T2] is Observable) = observe
        congruence(p, variant(p))
      }
    }
  }
}

// ==== Guarded state ====

class StringStateLoopsIsGuardedIterationTest
    extends GuardedIterationSpec("Kleisli[State[String, Option]] (guarded)", StringStateLoops) {
  def step[A: Sample]: Gen[Int -> String -> Option[(Either[A, Int], String)]] = StringStateFixture.guarded[A, Int]

  def step2[A: Sample]: Gen[Int -> String -> Option[(Either[Either[A, Int], Int], String)]] = {
    Gen.zip(StringStateFixture.guarded[Either[A, Int], Int], Sample.function[Int, A]).map { (p, stop) => x => s =>
      p(x)(s).map {
        case (Left(Right(y)), s2) if s2.length == s.length => (Left(Left(stop(y))), s2)
        case other                                         => other
      }
    }
  }

  def shrink: Int -> Int                  = _ / 2
  def bijection: (Int -> Int, Int -> Int) = (x => -x, x => -x)

  also("Elgot") {
    counterexample("fixedPoint", "for unguarded steps") {
      val observations = StringStateFixture.observe[Int, String]

      forAll(observations, Sample.function[Int, Boolean], Sample.function[Int, String]) { (observe, go, stop) =>
        given ((Int -> String -> Option[(String, String)]) is Observable)     = observe
        val unguarded: Int -> String -> Option[(Either[String, Int], String)] = {
          x => s => Some((if go(x) && x != 0 then Right(x / 2) else Left(stop(x)), s))
        }
        StringStateLoops.GuardedIterationLaws.fixedPoint(unguarded)
      }
    }
  }
}
