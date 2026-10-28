package parrot
package category

import org.scalacheck.Gen

import Sample.given

/** Steps on `Int` whose loops stop: a continuing step at least halves its state, so a loop takes at most 33 steps. */
object Descent {

  /** Lifts a terminating pure step so that every continuing step consumes a character, and stops on empty input. */
  def consuming[X, Y](f: X -> Either[Y, Int], stop: X -> Y): X -> String -> Option[(Either[Y, Int], String)] = {
    x => s =>
      f(x) match {
        case Left(y)                => Some((Left(y), s))
        case Right(n) if s.nonEmpty => Some((Right(n), s.tail))
        case Right(_)               => Some((Left(stop(x)), s))
      }
  }

  /** A state strictly closer to 0 than a nonzero *x*. */
  def below(x: Int, k: Int): Int = {
    x / (2 + (k % 3).abs)
  }

  /** Steps that stop with an *A* or continue closer to 0. */
  def step[A: Sample]: Gen[Int -> Either[A, Int]] = {
    for {
      stop <- Sample.function[Int, A]
      go   <- Sample.function[Int, Boolean]
      k    <- Sample.function[Int, Int]
    } yield (x: Int) => if x == 0 || !go(x) then Left(stop(x)) else Right(below(x, k(x)))
  }

  /** Steps with two ways to continue, both closer to 0. */
  def step2[A: Sample]: Gen[Int -> Either[Either[A, Int], Int]] = {
    for {
      stop  <- Sample.function[Int, A]
      which <- Sample.function[Int, Int]
      k     <- Sample.function[Int, Int]
    } yield (x: Int) =>
      if x == 0 then Left(Left(stop(x)))
      else
        (which(x) % 3).abs match {
          case 0 => Left(Left(stop(x)))
          case 1 => Left(Right(below(x, k(x))))
          case _ => Right(below(x, k(x)))
        }
  }

  /** Feedback steps on *A* + ℤ: from *A*, exit or enter the loop anywhere; inside, exit or move closer to 0. */
  def loop[A: Sample, B: Sample]: Gen[Either[A, Int] -> Either[B, Int]] = {
    for {
      exit  <- Sample.function[A, Either[B, Int]]
      inner <- step[B]
    } yield {
      case Left(a)  => exit(a)
      case Right(n) => inner(n)
    }
  }

  /** Feedback steps on *A* + (ℤ + ℤ), ordered lexicographically: the left loop may move to the right one. */
  def loop2[A: Sample, B: Sample]: Gen[Either[A, Either[Int, Int]] -> Either[B, Either[Int, Int]]] = {
    for {
      exit  <- Sample.function[A, Either[B, Either[Int, Int]]]
      left  <- step[Either[B, Int]]
      right <- step[B]
    } yield {
      case Left(a)        => exit(a)
      case Right(Left(n)) =>
        left(n) match {
          case Left(Left(b))  => Left(b)
          case Left(Right(m)) => Right(Right(m))
          case Right(m)       => Right(Left(m))
        }
      case Right(Right(n)) => right(n).map(Right(_))
    }
  }
}

/** The laws of [[Elgot]], with steps whose loops stop (in 𝒫) or that make progress (guarded instances). */
abstract class ElgotSpec(
  name: String,
  tracked val PF: PromonadFixture,
  tracked val E: Elgot { val S: Strong { val P: PF.P.type } },
)(using
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?=> Sample[E.S.M.Tensor[X, Y]],
) extends LawSuite("Elgot", name) {
  import types.{T2, T3, given}
  import PF.P
  import P.P
  import E.ElgotLaws.*
  import P.K.-->

  private given TensorSample: [X: Sample, Y: Sample] => Sample[E.S.M.Tensor[X, Y]] = tensor[X, Y]

  /** Steps whose iteration is defined. */
  def step[A: Sample]: Gen[P[Int, E.S.M.Tensor[A, Int]]]

  /** Steps with two ways to continue, for the double dagger law. */
  def step2[A: Sample]: Gen[P[Int, E.S.M.Tensor[E.S.M.Tensor[A, Int], Int]]]

  /** A pure map that keeps loops stopping: it does not move a state away from 0. */
  def shrink: Int --> Int

  /** A pure bijection that keeps loops stopping, with its inverse. */
  def bijection: (Int --> Int, Int --> Int)

  law("fixedPoint") {
    val observations = PF.observe[Int, T2]
    val ps           = step[T2]
    forAll(observations, ps) { (observe, p) =>
      given (P[Int, T2] is Observable) = observe
      fixedPoint(p)
    }
  }

  law("parameterNaturality") {
    val observations = PF.observe[Int, T3]
    val ps           = step[T2]
    val hs           = PF.base.arrow[T2, T3]
    forAll(observations, ps, hs) { (observe, p, h) =>
      given (P[Int, T3] is Observable) = observe
      parameterNaturality(p, h)
    }
  }

  law("composition") {
    val observations = PF.observe[Int, T2]
    val ps           = step[T2]
    forAll(observations, ps) { (observe, p) =>
      given (P[Int, T2] is Observable) = observe
      composition[T2, Int, Int](p, shrink)
    }
  }

  law("dinaturality") {
    val observations = PF.observe[Int, T2]
    val fs           = step[T2]
    val gs           = step[T2]
    forAll(observations, fs, gs) { (observe, f, g) =>
      given (P[Int, T2] is Observable) = observe
      dinaturality[T2, Int, Int](f, g)
    }
  }

  law("doubleDagger") {
    val observations = PF.observe[Int, T2]
    val ps           = step2[T2]
    forAll(observations, ps) { (observe, p) =>
      given (P[Int, T2] is Observable) = observe
      doubleDagger(p)
    }
  }

  law("uniformity") {
    val observations = PF.observe[Int, T2]
    val fs           = step[T2]
    forAll(observations, fs) { (observe, f) =>
      given (P[Int, T2] is Observable) = observe
      val (h, inverse)                          = bijection
      val g = P.multiply(E.S.second[Int, Int, T2](P.unit(h)), P.multiply(f, P.unit(inverse)))
      uniformity(f, g, h)
    }
  }

  law("congruence") {
    val observations = PF.observe[Int, T2]
    val ps           = step[T2]
    forAll(observations, ps) { (observe, p) =>
      given (P[Int, T2] is Observable) = observe
      congruence(p, PF.variant(p))
    }
  }
}

/** The laws of [[Traced]], with feedback that stops. */
abstract class TracedSpec(
  name: String,
  tracked val PF: PromonadFixture,
  tracked val T: Traced { val S: Strong { val P: PF.P.type } },
)(using
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?=> Sample[T.S.M.Tensor[X, Y]],
) extends LawSuite("Traced", name) {
  import types.{T1, T2, T3, T4, given}
  import PF.P
  import P.P
  import T.TracedLaws.*
  import P.K.-->

  private type +[X, Y] = T.S.M.Tensor[X, Y]

  private given TensorSample: [X: Sample, Y: Sample] => Sample[X + Y] = tensor[X, Y]

  /** Feedback steps on *A* ⊗ ℤ whose loops stop. */
  def loop[A: Sample, B: Sample]: Gen[P[A + Int, B + Int]]

  /** Feedback steps on *A* ⊗ (ℤ ⊗ ℤ) whose loops stop. */
  def loop2[A: Sample, B: Sample]: Gen[P[A + (Int + Int), B + (Int + Int)]]

  /** Arrows on *A* ⊗ *I*, which cannot loop. */
  def straight[A: Sample, B: Sample]: Gen[P[A + T.S.M.I, B + T.S.M.I]]

  /** A pure map that keeps loops stopping. */
  def shrink: Int --> Int

  /** Whether the trace is guarded: then it rejects feedback without progress, such as the braiding. */
  protected def guarded: Boolean = false

  private def yankingHolds: org.scalacheck.Prop = {
    val observations = PF.observe[T1, T1]
    forAll(observations) { observe =>
      given (P[T1, T1] is Observable) = observe
      yanking[T1]
    }
  }

  law("tightening") {
    val observations = PF.observe[T4, T3]
    val fs           = PF.arrow[T4, T1]
    val ps           = loop[T1, T2]
    val gs           = PF.arrow[T2, T3]
    forAll(observations, fs, ps, gs) { (observe, f, p, g) =>
      given (P[T4, T3] is Observable) = observe
      tightening(f, p, g)
    }
  }

  law("sliding") {
    val observations = PF.observe[T1, T2]
    val ps           = loop[T1, T2]
    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T2] is Observable) = observe
      sliding[T1, T2, Int, Int](p, shrink)
    }
  }

  law("vanishingUnit") {
    val observations = PF.observe[T1, T2]
    val ps           = straight[T1, T2]
    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T2] is Observable) = observe
      vanishingUnit(p)
    }
  }

  law("vanishingTensor") {
    val observations = PF.observe[T1, T2]
    val ps           = loop2[T1, T2]
    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T2] is Observable) = observe
      vanishingTensor[T1, T2, Int, Int](p)
    }
  }

  law("superposing") {
    val observations = PF.observe[T3 + T1, T4 + T2]
    val gs           = PF.base.arrow[T3, T4]
    val ps           = loop[T1, T2]
    forAll(observations, gs, ps) { (observe, g, p) =>
      given (P[T3 + T1, T4 + T2] is Observable) = observe
      superposing(g, p)
    }
  }

  if guarded then counterexample("yanking", "the braiding feeds back without progress")(yankingHolds)
  else law("yanking")(yankingHolds)

  law("congruence") {
    val observations = PF.observe[T1, T2]
    val ps           = loop[T1, T2]
    forAll(observations, ps) { (observe, p) =>
      given (P[T1, T2] is Observable) = observe
      congruence(p, PF.variant(p))
    }
  }
}

/** The laws of [[Recursion]], with functions that recurse on smaller arguments (𝒫) or after progress (guarded). */
abstract class RecursionSpec(
  name: String,
  tracked val PF: PromonadFixture,
  tracked val R: Recursion { val P: PF.P.type }
)(using types: SampleTypes) extends LawSuite("Recursion", name) {
  import types.{T2, given}
  import PF.P
  import P.P
  import R.RecursionLaws.*

  /** Functions from arrows to arrows whose fixed point is defined. */
  def guarded[B: Sample]: Gen[P[Int, B] -> P[Int, B]]

  law("fixedPoint") {
    val observations = PF.observe[Int, T2]
    val fs           = guarded[T2]
    forAll(observations, fs) { (observe, f) =>
      given (P[Int, T2] is Observable) = observe
      fixedPoint(f)
    }
  }

  law("familyFixedPoint", "two arrows, each calling the other") {
    val observations = PF.observe[Int, T2]
    val g0s          = guarded[T2]
    val g1s          = guarded[T2]
    forAll(observations, g0s, g1s) { (observe, g0, g1) =>
      given (P[Int, T2] is Observable) = observe
      familyFixedPoint[Int, T2](2)(rec => i => if i == 0 then g0(rec(1)) else g1(rec(0)))
    }
  }
}

/** The laws of [[Conway]], with arrows whose fixed points are defined. */
abstract class ConwaySpec(
  name: String,
  tracked val PF: PromonadFixture,
  tracked val C: Conway { val S: Strong { val P: PF.P.type } },
)(using
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?=> Sample[C.S.M.Tensor[X, Y]],
) extends LawSuite("Conway", name) {
  import types.{T2, T3, given}
  import PF.P
  import P.P
  import C.ConwayLaws.*
  import P.K.-->

  private type *[X, Y] = C.S.M.Tensor[X, Y]

  private given TensorSample: [X: Sample, Y: Sample] => Sample[X * Y] = tensor[X, Y]

  /** Arrows whose fixed point is defined. */
  def step[A: Sample]: Gen[P[A * Int, Int]]

  /** Arrows with two parameters whose fixed points are defined. */
  def step2[A: Sample]: Gen[P[(A * Int) * Int, Int]]

  /** A pure map that keeps fixed points defined. */
  def shrink: Int --> Int

  /** A pure bijection that keeps fixed points defined, with its inverse. */
  def bijection: (Int --> Int, Int --> Int)

  law("fixedPoint") {
    val observations = PF.observe[T2, Int]
    val ps           = step[T2]
    forAll(observations, ps) { (observe, p) =>
      given (P[T2, Int] is Observable) = observe
      fixedPoint(p)
    }
  }

  law("parameterNaturality") {
    val observations = PF.observe[T3, Int]
    val ps           = step[T2]
    val hs           = PF.base.arrow[T3, T2]
    forAll(observations, ps, hs) { (observe, p, h) =>
      given (P[T3, Int] is Observable) = observe
      parameterNaturality(p, h)
    }
  }

  law("composition") {
    val observations = PF.observe[T2, Int]
    val fs           = step[T2]
    forAll(observations, fs) { (observe, f) =>
      given (P[T2, Int] is Observable) = observe
      composition[T2, Int, Int](f, shrink)
    }
  }

  law("dinaturality") {
    val observations = PF.observe[T2, Int]
    val fs           = step[T2]
    val gs           = step[T2]
    forAll(observations, fs, gs) { (observe, f, g) =>
      given (P[T2, Int] is Observable) = observe
      dinaturality[T2, Int, Int](f, g)
    }
  }

  law("doubleDagger") {
    val observations = PF.observe[T2, Int]
    val ps           = step2[T2]
    forAll(observations, ps) { (observe, p) =>
      given (P[T2, Int] is Observable) = observe
      doubleDagger(p)
    }
  }

  law("uniformity") {
    val observations = PF.observe[T2, Int]
    val fs           = step[T2]
    forAll(observations, fs) { (observe, f) =>
      given (P[T2, Int] is Observable) = observe
      val (h, inverse)                          = bijection
      val g = P.multiply(P.unit(h), P.multiply(f, C.S.second[Int, Int, T2](P.unit(inverse))))
      uniformity(f, g, h)
    }
  }

  law("congruence") {
    val observations = PF.observe[T2, Int]
    val ps           = step[T2]
    forAll(observations, ps) { (observe, p) =>
      given (P[T2, Int] is Observable) = observe
      congruence(p, PF.variant(p))
    }
  }
}

// ==== 𝒫 ====

class PartialLoopsIsElgotTest extends ElgotSpec("Partial (while loops)", PartialProgramsFixture, Partial.Loops) {
  def step[A: Sample]: Gen[Int ~> Either[A, Int]]               = Descent.step[A].map(Partial(_))
  def step2[A: Sample]: Gen[Int ~> Either[Either[A, Int], Int]] = Descent.step2[A].map(Partial(_))
  def shrink: Int ~> Int                                        = Partial(_ / 2)
  def bijection: (Int ~> Int, Int ~> Int)                       = (Partial(x => -x), Partial(x => -x))
}

/** Iteration recovered from the trace of [[Partial.Loops]]: the bridge back. */
object PartialLoopsFromFeedback extends Elgot.OfTraced(Partial.Feedback)

class PartialFeedbackIsElgotTest
    extends ElgotSpec("Partial (iteration of the trace)", PartialProgramsFixture, PartialLoopsFromFeedback) {
  def step[A: Sample]: Gen[Int ~> Either[A, Int]]               = Descent.step[A].map(Partial(_))
  def step2[A: Sample]: Gen[Int ~> Either[Either[A, Int], Int]] = Descent.step2[A].map(Partial(_))
  def shrink: Int ~> Int                                        = Partial(_ / 2)
  def bijection: (Int ~> Int, Int ~> Int)                       = (Partial(x => -x), Partial(x => -x))
}

class PartialFeedbackIsTracedTest extends TracedSpec("Partial (feedback)", PartialProgramsFixture, Partial.Feedback) {
  def loop[A: Sample, B: Sample]: Gen[Either[A, Int] ~> Either[B, Int]] = Descent.loop[A, B].map(Partial(_))

  def loop2[A: Sample, B: Sample]: Gen[Either[A, Either[Int, Int]] ~> Either[B, Either[Int, Int]]] = {
    Descent.loop2[A, B].map(Partial(_))
  }

  def straight[A: Sample, B: Sample]: Gen[Either[A, Nothing] ~> Either[B, Nothing]] = {
    PartialFixture.arrow[Either[A, Nothing], Either[B, Nothing]]
  }

  def shrink: Int ~> Int = Partial(_ / 2)
}

class PartialKnotsIsRecursionTest extends RecursionSpec("Partial (knots)", PartialProgramsFixture, Partial.Knots) {
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

class StringStateLoopsIsElgotTest
    extends ElgotSpec("Kleisli[State[String, Option]] (guarded)", StringStateFixture, StringStateLoops) {
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

  counterexample("fixedPoint", "for unguarded steps") {
    val observations = StringStateFixture.observe[Int, String]
    forAll(observations, Sample.function[Int, Boolean], Sample.function[Int, String]) { (observe, go, stop) =>
      given ((Int -> String -> Option[(String, String)]) is Observable)     = observe
      val unguarded: Int -> String -> Option[(Either[String, Int], String)] = {
        x => s => Some((if go(x) && x != 0 then Right(x / 2) else Left(stop(x)), s))
      }
      StringStateLoops.ElgotLaws.fixedPoint(unguarded)
    }
  }
}

/** Feedback over [[StringStateLoops]]: guarded loops on *A* + *U*. */
object StringStateFeedback extends Traced.OfElgot(StringStateLoops)

class StringStateFeedbackIsTracedTest
    extends TracedSpec("Kleisli[State[String, Option]] (guarded feedback)", StringStateFixture, StringStateFeedback) {
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

class StringStateRecursionIsRecursionTest
    extends RecursionSpec("Kleisli[State[String, Option]] (guarded)", StringStateFixture, StringStateRecursion) {
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

// ==== 𝒫ᵒᵖ: the product column, by duality ====

/** Fixed points in 𝒫ᵒᵖ: the while loops of 𝒫, read backwards. */
object PartialFixedPoints extends Conway.OfElgot(Partial.Loops)

/** Feedback through products in 𝒫ᵒᵖ: the trace of [[PartialFixedPoints]]. */
object PartialProductFeedback extends Traced.OfConway(PartialFixedPoints)

/** The morphisms of 𝒫ᵒᵖ: total programs, reversed. */
object PartialOpBase extends Fixture("Partialᵒᵖ", PartialFixedPoints.S.P.K) {

  def arrow[X: Sample, Y: Sample]: Gen[Y ~> X] = PartialFixture.arrow[Y, X]

  def variant[X: Sample, Y: Sample](f: Y ~> X): Y ~> X = PartialFixture.variant(f)

  def observe[X: Sample, Y: Sample]: Gen[(Y ~> X) is Observable] = PartialFixture.observe[Y, X]
}

/** 𝒫ᵒᵖ as a promonad over itself, at its total programs. */
object PartialOpFixture extends PromonadFixture("Partialᵒᵖ", PartialFixedPoints.S.P) {
  val base: PartialOpBase.type = PartialOpBase

  def arrow[X: Sample, Y: Sample]: Gen[Y ~> X] = PartialFixture.arrow[Y, X]

  def variant[X: Sample, Y: Sample](p: Y ~> X): Y ~> X = PartialFixture.variant(p)

  def observe[X: Sample, Y: Sample]: Gen[(Y ~> X) is Observable] = PartialFixture.observe[Y, X]
}

class PartialOpIsConwayTest
    extends ConwaySpec("Partialᵒᵖ (loops read backwards)", PartialOpFixture, PartialFixedPoints) {
  def step[A: Sample]: Gen[Int ~> Either[A, Int]]               = Descent.step[A].map(Partial(_))
  def step2[A: Sample]: Gen[Int ~> Either[Either[A, Int], Int]] = Descent.step2[A].map(Partial(_))
  def shrink: Int ~> Int                                        = Partial(_ / 2)
  def bijection: (Int ~> Int, Int ~> Int)                       = (Partial(x => -x), Partial(x => -x))
}

class PartialOpIsTracedTest
    extends TracedSpec("Partialᵒᵖ (feedback through products)", PartialOpFixture, PartialProductFeedback) {
  def loop[A: Sample, B: Sample]: Gen[Either[B, Int] ~> Either[A, Int]] = Descent.loop[B, A].map(Partial(_))

  def loop2[A: Sample, B: Sample]: Gen[Either[B, Either[Int, Int]] ~> Either[A, Either[Int, Int]]] = {
    Descent.loop2[B, A].map(Partial(_))
  }

  def straight[A: Sample, B: Sample]: Gen[Either[B, Nothing] ~> Either[A, Nothing]] = {
    PartialFixture.arrow[Either[B, Nothing], Either[A, Nothing]]
  }

  def shrink: Int ~> Int = Partial(_ / 2)
}
