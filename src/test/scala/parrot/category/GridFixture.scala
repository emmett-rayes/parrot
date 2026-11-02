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

// ==== 𝒫ᵒᵖ: the product column, by duality ====

/** Fixed points in 𝒫ᵒᵖ: the while loops of 𝒫, read backwards. */
object PartialFixedPoints extends Conway.OfElgot(Partial.Loops)

/** Feedback through products in 𝒫ᵒᵖ: the trace of [[PartialFixedPoints]]. */
object PartialProductFeedback extends Traced.OfConway(PartialFixedPoints)

/** The morphisms of 𝒫ᵒᵖ: total programs, reversed. */
object PartialOpBase extends CategoryFixture("Partialᵒᵖ", PartialFixedPoints.strong.profunctor.category) {

  def arrow[X: Sample, Y: Sample]: Gen[Y ~> X] = PartialFixture.arrow[Y, X]

  def variant[X: Sample, Y: Sample](f: Y ~> X): Y ~> X = PartialFixture.variant(f)

  def observe[X: Sample, Y: Sample]: Gen[(Y ~> X) is Observable] = PartialFixture.observe[Y, X]
}

/** 𝒫ᵒᵖ as a promonad over itself, at its total programs. */
object PartialOpFixture extends PromonadFixture("Partialᵒᵖ", PartialFixedPoints.strong.profunctor) {
  val category: PartialOpBase.type = PartialOpBase

  def arrow[X: Sample, Y: Sample]: Gen[Y ~> X] = PartialFixture.arrow[Y, X]

  def variant[X: Sample, Y: Sample](p: Y ~> X): Y ~> X = PartialFixture.variant(p)

  def observe[X: Sample, Y: Sample]: Gen[(Y ~> X) is Observable] = PartialFixture.observe[Y, X]
}
