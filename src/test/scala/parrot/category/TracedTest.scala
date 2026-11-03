package parrot
package category

import org.scalacheck.Gen

import Sample.given
import Category.Type

/** The laws of [[Traced]], with feedback that stops. */
abstract class TracedSpec(
  name: String,
  tracked val traced: Traced.On[Bistrong.On[Promonad.On[Category { type Obj = Type }]]],
)(using
  promonad: PromonadFixture.For[traced.strong.profunctor.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[traced.strong.monoidal.Tensor[X, Y]],
) extends LawSuite("Traced", name) {
  import types.{T1, T2, T3, T4, given}
  import promonad.*
  import traced.strong.profunctor
  import profunctor.P
  import traced.TracedLaws.*
  import profunctor.category.-->

  private type +[X, Y] = traced.strong.monoidal.Tensor[X, Y]

  private given TensorSample: [X: Sample, Y: Sample] => Sample[X + Y] = tensor[X, Y]

  /** Feedback steps on *A* ⊗ ℤ whose loops stop. */
  def loop[A: Sample, B: Sample]: Gen[P[A + Int, B + Int]]

  /** Feedback steps on *A* ⊗ (ℤ ⊗ ℤ) whose loops stop. */
  def loop2[A: Sample, B: Sample]: Gen[P[A + (Int + Int), B + (Int + Int)]]

  /** Arrows on *A* ⊗ *I*, which cannot loop. */
  def straight[A: Sample, B: Sample]: Gen[P[A + traced.strong.monoidal.I, B + traced.strong.monoidal.I]]

  /** A pure map that keeps loops stopping. */
  def shrink: Int --> Int

  /** Whether the trace is guarded: then it rejects feedback without progress, such as the braiding. */
  protected def guarded: Boolean = false

  private def yankingHolds: org.scalacheck.Prop = {
    val observations = observe[T1, T1]

    forAll(observations) { observe =>
      given (P[T1, T1] is Observable) = observe
      yanking[T1]
    }
  }

  law("tightening") {
    val observations = observe[T4, T3]
    val fs           = arrow[T4, T1]
    val ps           = loop[T1, T2]
    val gs           = arrow[T2, T3]

    forAll(observations, fs, ps, gs) { (observe, f, p, g) =>
      given (P[T4, T3] is Observable) = observe
      tightening(f, p, g)
    }
  }

  law("sliding") {
    val observations = observe[T1, T2]
    val ps           = loop[T1, T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T2] is Observable) = observe
      sliding[T1, T2, Int, Int](p, shrink)
    }
  }

  law("vanishingUnit") {
    val observations = observe[T1, T2]
    val ps           = straight[T1, T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T2] is Observable) = observe
      vanishingUnit(p)
    }
  }

  law("vanishingTensor") {
    val observations = observe[T1, T2]
    val ps           = loop2[T1, T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T2] is Observable) = observe
      vanishingTensor[T1, T2, Int, Int](p)
    }
  }

  law("superposing") {
    val observations = observe[T3 + T1, T4 + T2]
    val gs           = category.arrow[T3, T4]
    val ps           = loop[T1, T2]

    forAll(observations, gs, ps) { (observe, g, p) =>
      given (P[T3 + T1, T4 + T2] is Observable) = observe
      superposing(g, p)
    }
  }

  if guarded then counterexample("yanking", "the braiding feeds back without progress")(yankingHolds)
  else law("yanking")(yankingHolds)

  law("congruence") {
    val observations = observe[T1, T2]
    val ps           = loop[T1, T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T2] is Observable) = observe
      congruence(p, variant(p))
    }
  }
}

// ==== 𝒫 ====

class PartialFeedbackIsTracedTest extends TracedSpec("Partial (feedback)", Partial.Feedback) {
  def loop[A: Sample, B: Sample]: Gen[Either[A, Int] ~> Either[B, Int]] = Descent.loop[A, B].map(Partial.fromTotal(_))

  def loop2[A: Sample, B: Sample]: Gen[Either[A, Either[Int, Int]] ~> Either[B, Either[Int, Int]]] = {
    Descent.loop2[A, B].map(Partial.fromTotal(_))
  }

  def straight[A: Sample, B: Sample]: Gen[Either[A, Nothing] ~> Either[B, Nothing]] = {
    PartialFixture.arrow[Either[A, Nothing], Either[B, Nothing]]
  }

  def shrink: Int ~> Int = Partial.fromTotal(_ / 2)
}

// ==== Guarded state ====

/** Feedback over [[StringStateLoops]]: guarded loops on *A* + *U*. */
object StringStateFeedback extends Traced.OfElgot(StringStateLoops)

class StringStateFeedbackIsTracedTest
    extends TracedSpec("Kleisli[State[String, Option]] (guarded feedback)", StringStateFeedback) {
  override protected def guarded: Boolean = true

  def loop[A: Sample, B: Sample]: Gen[Either[A, Int] -> String -> Option[(Either[B, Int], String)]] = {
    Gen.zip(Descent.loop[A, B], Sample.function[Either[A, Int], B]).map {
      (f: Either[A, Int] -> Either[B, Int], stop: Either[A, Int] -> B) => Descent.consuming(f, stop)
    }
  }

  def loop2[A: Sample, B: Sample]
    : Gen[Either[A, Either[Int, Int]] -> String -> Option[(Either[B, Either[Int, Int]], String)]] = {
    Gen.zip(Descent.loop2[A, B], Sample.function[Either[A, Either[Int, Int]], B]).map {
      (f: Either[A, Either[Int, Int]] -> Either[B, Either[Int, Int]], stop: Either[A, Either[Int, Int]] -> B) =>
        (x: Either[A, Either[Int, Int]]) => (s: String) =>
          f(x) match {
            case Left(b)                => Some((Left(b), s))
            case Right(u) if s.nonEmpty => Some((Right(u), s.tail))
            case Right(_)               => Some((Left(stop(x)), s))
          }
    }
  }

  def straight[A: Sample, B: Sample]: Gen[Either[A, Nothing] -> String -> Option[(Either[B, Nothing], String)]] = {
    StringStateFixture.arrow[Either[A, Nothing], Either[B, Nothing]]
  }

  def shrink: Int -> Int = _ / 2
}

// ==== 𝒫ᵒᵖ: the product column, by duality ====

class PartialOpIsTracedTest
    extends TracedSpec("Partialᵒᵖ (feedback through products)", PartialProductFeedback) {
  def loop[A: Sample, B: Sample]: Gen[Either[B, Int] ~> Either[A, Int]] = Descent.loop[B, A].map(Partial.fromTotal(_))

  def loop2[A: Sample, B: Sample]: Gen[Either[B, Either[Int, Int]] ~> Either[A, Either[Int, Int]]] = {
    Descent.loop2[B, A].map(Partial.fromTotal(_))
  }

  def straight[A: Sample, B: Sample]: Gen[Either[B, Nothing] ~> Either[A, Nothing]] = {
    PartialFixture.arrow[Either[B, Nothing], Either[A, Nothing]]
  }

  def shrink: Int ~> Int = Partial.fromTotal(_ / 2)
}
