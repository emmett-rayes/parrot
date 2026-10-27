package parrot
package category

import org.scalacheck.Gen

import Sample.given

/** States are remaining inputs, measured by their length: a step that consumes input makes progress. */
given StringIsMeasure: String is Measure {
  def measure(s: String): Int = s.length
}

/** Computations that consume a string and may fail: the shape of a parser without diagnostics. */
object StringState extends StateT[String](Monad.OptionIsMonad)

/** The Kleisli arrows of [[StringState]]. */
object StringStateKleisli extends Kleisli(StringState)

/** Failure, backtracking choice and lookahead for [[StringState]]. */
object StringStateClassical extends StateT.ClassicalOf(StringState, ClassicalMonad.OptionIsClassical)

/** The classical restriction structure of [[StringStateKleisli]]. */
object StringStateDomains extends Kleisli.ClassicalOf(StringStateKleisli, StringStateClassical)

/** The arrows of [[StringStateKleisli]], run on one side of a tagged union. */
object StringStateChoice extends Kleisli.CoproductStrength(StringStateKleisli)

/** Guarded loops over [[StringState]]. */
object StringStateIteration extends StateT.GuardedIteration(StringState, ClassicalMonad.OptionIsClassical)

/** The guarded iteration of [[StringStateKleisli]]. */
object StringStateLoops extends Kleisli.ElgotOf(StringStateChoice, StringStateIteration)

/** Guarded recursion for [[StringStateKleisli]]. */
object StringStateRecursion extends StateT.GuardedRecursion(StringStateKleisli, ClassicalMonad.OptionIsClassical)

object StringStateFixture extends PromonadFixture("Kleisli[State[String, Option]]", StringStateKleisli) {
  val base: TotalFixture.type = TotalFixture

  /** Short inputs over a small alphabet. */
  val states: Gen[String] = Gen.choose(0, 5).flatMap(n => Gen.listOfN(n, Gen.oneOf('a', 'b')).map(_.mkString))

  /** Arrows that fail, or succeed after consuming up to two characters. */
  def arrow[X: Sample, Y: Sample]: Gen[X -> String -> Option[(Y, String)]] = {
    val outcomes = Gen.frequency(1 -> Gen.const(None), 3 -> Gen.zip(Y.gen, Gen.choose(0, 2)).map(Some(_)))
    Gen.function1[(X, String), Option[(Y, Int)]](outcomes)(using Sample.Tuple2Sample[X, String].cogen).map {
      f => x => s => f((x, s)).map((y, k) => (y, s.drop(k)))
    }
  }

  def variant[X: Sample, Y: Sample](p: X -> String -> Option[(Y, String)]): X -> String -> Option[(Y, String)] = {
    x => s => p(x)(s)
  }

  def observe[X: Sample, Y: Sample]: Gen[(X -> String -> Option[(Y, String)]) is Observable] = {
    Gen.listOfN(6, Gen.zip(X.gen, states)).map { points =>
      Observable.through[X -> String -> Option[(Y, String)], Option[(Y, String)]](
        points.map((x, s) => p => p(x)(s))
      )(using Observable.EqIsObservable(using Eq.OptionIsEq(using Eq.Tuple2IsEq(using Y.eq, Eq.StringIsEq))))
    }
  }

  /** Guarded steps: they stop with an *A*, or continue with an *X* after consuming at least one character. */
  def guarded[A: Sample, X: Sample]: Gen[X -> String -> Option[(Either[A, X], String)]] = {
    val outcomes = Gen.frequency(
      1 -> Gen.const(None),
      2 -> Gen.zip(A.gen, Gen.choose(0, 1)).map((a, k) => Some(Left((a, k)))),
      3 -> Gen.zip(X.gen, Gen.choose(1, 2)).map((x, k) => Some(Right((x, k)))),
    )
    Gen.zip(
      Gen.function1[(X, String), Option[Either[(A, Int), (X, Int)]]](outcomes)(using
        Sample.Tuple2Sample[X, String].cogen
      ),
      Sample.function[X, A],
    ).map { (f: ((X, String)) -> Option[Either[(A, Int), (X, Int)]], stop: X -> A) => (x: X) => (s: String) =>
      f((x, s)).map {
        case Left((a, k))                 => (Left(a), s.drop(k))
        case Right((x2, k)) if s.nonEmpty => (Right(x2), s.drop(k))
        case Right(_)                     => (Left(stop(x)), s)
      }
    }
  }
}
