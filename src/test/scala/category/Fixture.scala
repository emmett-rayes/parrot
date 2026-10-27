package parrot
package category

import org.scalacheck.{Arbitrary, Cogen, Gen}

/** What law tests need to know about a type: how to generate its values, how to vary functions by them, and how to
  * compare them.
  */
final class Sample[X](val gen: Gen[X], val cogen: Cogen[X], val eq: X is Eq, val inhabited: Boolean = true)

object Sample {

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

  /** Samples of pairs from samples of their components, for all component types: the samples of the carrier of a
    * bifunctor.
    */
  given Tuple2Samples: ([X, Y] => (Sample[X], Sample[Y]) ?=> Sample[(X, Y)]) = {
    [X, Y] => (_: Sample[X], _: Sample[Y]) ?=> Tuple2Sample[X, Y]
  }

  /** Samples of tagged unions from samples of their alternatives, for all alternative types. */
  given EitherSamples: ([X, Y] => (Sample[X], Sample[Y]) ?=> Sample[Either[X, Y]]) = {
    [X, Y] => (_: Sample[X], _: Sample[Y]) ?=> EitherSample[X, Y]
  }

  /** Samples of optional values from samples of their values, for all value types: the samples of a monad. */
  given OptionSamples: ([X] => Sample[X] ?=> Sample[Option[X]]) = {
    [X] => (_: Sample[X]) ?=> OptionSample[X]
  }

  /** Samples of pairs with a first component of type *A*, for all second components: the samples of a writer monad. */
  given WriterSamples: [A: Sample] => ([X] => Sample[X] ?=> Sample[(A, X)]) = {
    [X] => (_: Sample[X]) ?=> Tuple2Sample[A, X]
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

/** Generators, variants and observations for the morphisms of a category whose objects are all types. */
abstract class Fixture(val name: String, tracked val K: Category { type Obj = Type }) extends caps.Pure {
  import K.-->

  /** Generates morphisms *X* → *Y*, including the cases that matter for the category (failure, effects). */
  def arrow[X: Sample, Y: Sample]: Gen[X --> Y]

  /** A morphism equal to *f* by construction, but a different value. */
  def variant[X: Sample, Y: Sample](f: X --> Y): X --> Y

  /** Observations of morphisms *X* → *Y*, at sample points chosen afresh for every property. */
  def observe[X: Sample, Y: Sample]: Gen[(X --> Y) is Observable]
}

/** 𝒮: generated pure functions, observed by application. */
object TotalFixture extends Fixture("Total", Total) {

  def arrow[X: Sample, Y: Sample]: Gen[X -> Y] = {
    Sample.function
  }

  def variant[X: Sample, Y: Sample](f: X -> Y): X -> Y = {
    x => f(x)
  }

  def observe[X: Sample, Y: Sample]: Gen[(X -> Y) is Observable] = {
    Sample.points[X].map { points =>
      Observable.total(points)(using Observable.EqIsObservable(using Y.eq))
    }
  }
}

/** 𝒫, at its total morphisms: divergence cannot be observed by a test that terminates. */
object PartialFixture extends Fixture("Partial", Partial) {

  def arrow[X: Sample, Y: Sample]: Gen[X ~> Y] = {
    Sample.function[X, Y].map(Partial(_))
  }

  def variant[X: Sample, Y: Sample](f: X ~> Y): X ~> Y = {
    Partial(x => f.run(x))
  }

  def observe[X: Sample, Y: Sample]: Gen[(X ~> Y) is Observable] = {
    Sample.points[X].map { points =>
      Observable.partial(points)(using Observable.EqIsObservable(using Y.eq))
    }
  }
}

/** The opposite of a fixture's category: arrows *X* → *Y* are arrows *Y* → *X* of the original. */
final class OpFixture(tracked val F: Fixture) extends Fixture(s"${F.name}ᵒᵖ", F.K.op) {
  import F.K.-->

  def arrow[X: Sample, Y: Sample]: Gen[Y --> X] = {
    F.arrow
  }

  def variant[X: Sample, Y: Sample](f: Y --> X): Y --> X = {
    F.variant(f)
  }

  def observe[X: Sample, Y: Sample]: Gen[(Y --> X) is Observable] = {
    F.observe
  }
}

/** Generators, variants and observations for the arrows of a promonad over a category whose objects are all types. */
abstract class PromonadFixture(val name: String, tracked val P: Promonad { val K: Category { type Obj = Type } })
    extends caps.Pure {
  import P.P

  /** The fixture of the base category, for pure arrows. */
  val base: Fixture { val K: P.K.type }

  /** Generates arrows *X* → *Y*, including the cases that matter for the promonad (failure, effects). */
  def arrow[X: Sample, Y: Sample]: Gen[P[X, Y]]

  /** An arrow equal to *p* by construction, but a different value. */
  def variant[X: Sample, Y: Sample](p: P[X, Y]): P[X, Y]

  /** Observations of arrows *X* → *Y*, at sample points chosen afresh for every property. */
  def observe[X: Sample, Y: Sample]: Gen[P[X, Y] is Observable]

  /** The same generators, for the category of arrows. */
  final lazy val category: Fixture { val K: P.category.type } = PromonadFixture.Category(this)
}

object PromonadFixture {

  /** The fixture of the category of arrows of a promonad. */
  final class Category(tracked val F: PromonadFixture) extends Fixture(F.name, F.P.category) {
    import F.P.P

    def arrow[X: Sample, Y: Sample]: Gen[P[X, Y]] = {
      F.arrow[X, Y]
    }

    def variant[X: Sample, Y: Sample](p: P[X, Y]): P[X, Y] = {
      F.variant[X, Y](p)
    }

    def observe[X: Sample, Y: Sample]: Gen[P[X, Y] is Observable] = {
      F.observe[X, Y]
    }
  }
}

/** `Kleisli[Option]`: functions that fail often enough for failure to matter. */
object OptionKleisliFixture extends PromonadFixture("Kleisli[Option]", Kleisli.OptionKleisli) {
  val base: TotalFixture.type = TotalFixture

  def arrow[X: Sample, Y: Sample]: Gen[X -> Option[Y]] = {
    val results = Gen.frequency(1 -> Gen.const(None), 3 -> Y.gen.map(Some(_)))
    Gen.function1[X, Option[Y]](results)(using X.cogen)
  }

  def variant[X: Sample, Y: Sample](p: X -> Option[Y]): X -> Option[Y] = {
    x => p(x)
  }

  def observe[X: Sample, Y: Sample]: Gen[(X -> Option[Y]) is Observable] = {
    TotalFixture.observe[X, Option[Y]]
  }
}
