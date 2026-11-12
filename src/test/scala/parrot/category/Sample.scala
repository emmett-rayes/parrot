package parrot
package category

import org.scalacheck.{Arbitrary, Cogen, Gen}

/** What law tests need to know about a type: how to generate its values, how to vary functions by them, and how to
  * compare them.
  */
final class Sample[X](val gen: Gen[X], val cogen: Cogen[X], val eq: X is Eq, val inhabited: Boolean = true)

object Sample {
  import Category.Discrete2.Disc2
  import Category.Empty.Absurd
  import Product.Components

  /** The number of generated points per function observation. */
  private val points: Int = 10

  given [X: {Arbitrary, Cogen, Eq}] => Sample[X] = {
    Sample(summon[Arbitrary[X]].arbitrary, summon[Cogen[X]], summon[X is Eq])
  }

  given IntSample: Sample[Int]         = summon
  given LongSample: Sample[Long]       = summon
  given BooleanSample: Sample[Boolean] = summon
  given StringSample: Sample[String]   = summon
  given UnitSample: Sample[Unit]       = summon

  /** `Double`, often at the values whose equality is special: `NaN`, `0.0` and `-0.0`. */
  given DoubleSample: Sample[Double] = {
    val special = Gen.oneOf(Double.NaN, 0.0, -0.0)
    Sample(Gen.frequency(1 -> special, 2 -> Arbitrary.arbitrary[Double]), Cogen[Double], Eq.DoubleIsEq)
  }

  /** `Nothing` has no values: it is never generated. */
  given NothingSample: Sample[Nothing] = {
    Sample(Gen.fail, Cogen[Nothing](n => n), Eq.NothingIsEq, inhabited = false)
  }

  given OptionSample: [A: Sample] => Sample[Option[A]] = {
    Sample(Gen.option(A.gen), Cogen.cogenOption(using A.cogen), Eq.OptionIsEq(using A.eq))
  }

  given Tuple2Sample: [A: Sample, B: Sample] => Sample[(A, B)] = {
    Sample(
      Gen.zip(A.gen, B.gen),
      Cogen.tuple2(using A.cogen, B.cogen),
      Eq.Tuple2IsEq(using A.eq, B.eq),
      A.inhabited && B.inhabited,
    )
  }

  given EitherSample: [A: Sample, B: Sample] => Sample[Either[A, B]] = {
    val gen = (A.inhabited, B.inhabited) match {
      case (true, true)  => Gen.oneOf(A.gen.map(Left(_)), B.gen.map(Right(_)))
      case (true, false) => A.gen.map(Left(_))
      case (false, true) => B.gen.map(Right(_))
      case _             => Gen.fail
    }
    new Sample(
      gen,
      Cogen.cogenEither(using A.cogen, B.cogen),
      Eq.EitherIsEq(using A.eq, B.eq),
      A.inhabited || B.inhabited
    )
  }

  /** Functions on `Boolean`, which are data: a function is determined by its two values. */
  given BooleanFunctionSample: [Y: Sample] => Sample[Boolean -> Y] = {
    val values: (Boolean -> Y) -> (Y, Y) = f => (f(false), f(true))
    val functionIsEq: (Boolean -> Y) is Eq = new Eq {
      type Self = Boolean -> Y

      def equal(f: Boolean -> Y, g: Boolean -> Y): Boolean = {
        Y.eq.equal(f(false), g(false)) && Y.eq.equal(f(true), g(true))
      }
    }
    Sample(
      Gen.zip(Y.gen, Y.gen).map((no: Y, yes: Y) => (b: Boolean) => if b then yes else no),
      Cogen.tuple2(using Y.cogen, Y.cogen).contramap(values),
      functionIsEq,
      Y.inhabited,
    )
  }

  /** Families of points of a diagram (*X*,*Y*) of shape **2**, which are data: a family is determined by its two
    * points.
    */
  given Discrete2FamilySample: [X: Sample, Y: Sample] => Sample[[A] -> (A is Disc2) ?-> Components[X, Y][A]] = {
    def family(x: X, y: Y): [A] -> (A is Disc2) ?-> Components[X, Y][A] = {
      [A] => (a: A is Disc2) ?=> {
        a.index match {
          case Disc2.Index.Zero => x
          case Disc2.Index.One  => y
        }
      }
    }
    val points: ([A] -> (A is Disc2) ?-> Components[X, Y][A]) -> (X, Y) = p => (p[0], p[1])
    val familyIsEq: ([A] -> (A is Disc2) ?-> Components[X, Y][A]) is Eq = new Eq {
      type Self = [A] -> (A is Disc2) ?-> Components[X, Y][A]

      def equal(p: Self, q: Self): Boolean = {
        X.eq.equal(p[0], q[0]) && Y.eq.equal(p[1], q[1])
      }
    }
    Sample(
      Gen.zip(X.gen, Y.gen).map(family),
      Cogen.tuple2(using X.cogen, Y.cogen).contramap(points),
      familyIsEq,
      X.inhabited && Y.inhabited,
    )
  }

  /** The family of points of the empty diagram, the only one: it has no points. */
  given EmptyFamilySample: Sample[[A] -> (A is Absurd) ?-> Nothing] = {
    val empty: [A] -> (A is Absurd) ?-> Nothing = [A] => (a: A is Absurd) ?=> a.absurd
    val familyIsEq: ([A] -> (A is Absurd) ?-> Nothing) is Eq = new Eq {
      type Self = [A] -> (A is Absurd) ?-> Nothing

      def equal(p: Self, q: Self): Boolean = {
        true
      }
    }
    Sample(Gen.const(empty), Cogen[Unit].contramap(_ => ()), familyIsEq)
  }

  /** Points of the sum of a diagram (*X*,*Y*) of shape **2**, which are data: a point is determined by its object and
    * its point there, as a tagged union is.
    */
  given Discrete2ExistsSample: [X: Sample, Y: Sample] => Sample[Total.Exists[Disc2, Components[X, Y]]] = {
    def tagged[A](a: A is Disc2, x: Components[X, Y][A]): Either[X, Y] = {
      a.index match {
        case Disc2.Index.Zero => Left(summon[A =:= 0].substituteCo[[T] =>> Components[X, Y][T]](x))
        case Disc2.Index.One  => Right(summon[A =:= 1].substituteCo[[T] =>> Components[X, Y][T]](x))
      }
    }
    val either: Total.Exists[Disc2, Components[X, Y]] -> Either[X, Y] = s => tagged[s.A](s.obj, s.at)
    val exists: Either[X, Y] -> Total.Exists[Disc2, Components[X, Y]] = {
      case Left(x)  => Total.Exists[Disc2, Components[X, Y], 0](Disc2.Zero, x)
      case Right(y) => Total.Exists[Disc2, Components[X, Y], 1](Disc2.One, y)
    }
    val eithers = EitherSample[X, Y]
    val existsIsEq: Total.Exists[Disc2, Components[X, Y]] is Eq = new Eq {
      type Self = Total.Exists[Disc2, Components[X, Y]]

      def equal(s: Self, t: Self): Boolean = {
        eithers.eq.equal(either(s), either(t))
      }
    }
    Sample(eithers.gen.map(exists), eithers.cogen.contramap(either), existsIsEq, eithers.inhabited)
  }

  /** The sum of the empty diagram, which has no points: it is never generated. */
  given EmptyExistsSample: Sample[Total.Exists[Absurd, [A] =>> Nothing]] = {
    val existsIsEq: Total.Exists[Absurd, [A] =>> Nothing] is Eq = new Eq {
      type Self = Total.Exists[Absurd, [A] =>> Nothing]

      def equal(s: Self, t: Self): Boolean = {
        true
      }
    }
    Sample(Gen.fail, Cogen[Unit].contramap(_ => ()), existsIsEq, inhabited = false)
  }

  /** Samples of pairs from samples of their components, for all component types: the samples of the carrier of a
    * bifunctor.
    */
  given Tuple2Samples: ([X, Y] => (Sample[X], Sample[Y]) ?-> Sample[(X, Y)]) = {
    [X, Y] => (_: Sample[X], _: Sample[Y]) ?=> Tuple2Sample[X, Y]
  }

  /** Samples of families of points of shape **2** from samples of their points, for all point types: the samples of
    * the carrier of the products of limits.
    */
  given Discrete2FamilySamples
    : ([X, Y] => (Sample[X], Sample[Y]) ?-> Sample[[A] -> (A is Disc2) ?-> Components[X, Y][A]]) = {
    [X, Y] => (_: Sample[X], _: Sample[Y]) ?=> Discrete2FamilySample[X, Y]
  }

  /** Samples of sums of shape **2** from samples of their points, for all point types: the samples of the carrier of
    * the coproducts of colimits.
    */
  given Discrete2ExistsSamples: ([X, Y] => (Sample[X], Sample[Y]) ?-> Sample[Total.Exists[Disc2, Components[X, Y]]]) = {
    [X, Y] => (_: Sample[X], _: Sample[Y]) ?=> Discrete2ExistsSample[X, Y]
  }

  /** Samples of tagged unions from samples of their alternatives, for all alternative types. */
  given EitherSamples: ([X, Y] => (Sample[X], Sample[Y]) ?-> Sample[Either[X, Y]]) = {
    [X, Y] => (_: Sample[X], _: Sample[Y]) ?=> EitherSample[X, Y]
  }

  /** Samples of optional values from samples of their values, for all value types: the samples of a monad. */
  given OptionSamples: ([X] => Sample[X] ?-> Sample[Option[X]]) = {
    [X] => (_: Sample[X]) ?=> OptionSample[X]
  }

  /** Optional optional samples, for all types: the samples of `Option` ∘ `Option`. */
  given OptionOptionSamples: ([X] => Sample[X] ?-> Sample[Option[Option[X]]]) = {
    [X] => (_: Sample[X]) ?=> OptionSample[Option[X]]
  }

  /** Samples of pairs with a first component of type *A*, for all second components: the samples of a writer monad. */
  given WriterSamples: [A: Sample] => ([X] => Sample[X] ?-> Sample[(A, X)]) = {
    [X] => (_: Sample[X]) ?=> Tuple2Sample[A, X]
  }

  /** Samples of pairs with a first component of type *A* and an optional second, for all second components: the
    * samples of a failure transformer over a writer monad.
    */
  given FailingWriterSamples: [A: Sample] => ([X] => Sample[X] ?-> Sample[(A, Option[X])]) = {
    [X] => (_: Sample[X]) ?=> Tuple2Sample[A, Option[X]]
  }

  /** Optional samples of pairs with a first component of type *A*, for all second components: the samples of a writer
    * transformer over `Option`.
    */
  given WriterOverOptionSamples: [A: Sample] => ([X] => Sample[X] ?-> Sample[Option[(A, X)]]) = {
    [X] => (_: Sample[X]) ?=> OptionSample[(A, X)]
  }

  /** Samples of computations on `Boolean` states, for all result types: the samples of a state monad. */
  given BooleanStateSamples: ([X] => Sample[X] ?-> Sample[Boolean -> (X, Boolean)]) = {
    [X] => (_: Sample[X]) ?=> BooleanFunctionSample[(X, Boolean)]
  }

  /** Samples of computations on `Boolean` states that may fail, for all result types: the samples of a state
    * transformer over `Option`.
    */
  given FailingBooleanStateSamples: ([X] => Sample[X] ?-> Sample[Boolean -> Option[(X, Boolean)]]) = {
    [X] => (_: Sample[X]) ?=> BooleanFunctionSample[Option[(X, Boolean)]]
  }

  /** Samples of the values themselves, for all types: the samples of a functor that is the identity on objects. */
  given IdentitySamples: ([X] => Sample[X] ?-> Sample[X]) = {
    [X] => (x: Sample[X]) ?=> x
  }

  given SeqSample: [A: Sample] => Sample[Seq[A]] = {
    Sample(Gen.listOf(A.gen), Cogen.cogenSeq(using A.cogen), Eq.SeqIsEq[Seq, A](using A.eq))
  }

  /** Sample points for the observation of a function: a fresh list for every property. */
  def points[X: Sample]: Gen[List[X]] = {
    if X.inhabited then Gen.listOfN(points, X.gen) else Gen.const(Nil)
  }

  /** Pure functions *X* → *Y*, varying with their argument. */
  def function[X: Sample, Y: Sample]: Gen[X -> Y] = {
    Gen.function1[X, Y](Y.gen)(using X.cogen)
  }
}
