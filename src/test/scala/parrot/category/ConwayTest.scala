package parrot
package category

import org.scalacheck.Gen

import Sample.given
import Category.Type

/** The laws of [[Conway]], with arrows whose fixed points are defined. */
abstract class ConwaySpec(
  name: String,
  tracked val conway: Conway.On[Bistrong.On[Promonad.On[Category { type Obj = Type }]]],
)(using
  promonad: PromonadFixture.For[conway.strong.profunctor.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[conway.strong.monoidal.Tensor[X, Y]],
) extends LawSuite("Conway", name) {
  import types.{T2, T3, given}
  import promonad.*
  import conway.strong.profunctor
  import profunctor.{P, >>>}
  import conway.ConwayLaws.*
  import profunctor.category.-->

  private type *[X, Y] = conway.strong.monoidal.Tensor[X, Y]

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
    val observations = observe[T2, Int]
    val ps           = step[T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T2, Int] is Observable) = observe
      fixedPoint(p)
    }
  }

  law("parameterNaturality") {
    val observations = observe[T3, Int]
    val ps           = step[T2]
    val hs           = category.arrow[T3, T2]

    forAll(observations, ps, hs) { (observe, p, h) =>
      given (P[T3, Int] is Observable) = observe
      parameterNaturality(p, h)
    }
  }

  law("composition") {
    val observations = observe[T2, Int]
    val fs           = step[T2]

    forAll(observations, fs) { (observe, f) =>
      given (P[T2, Int] is Observable) = observe
      composition[T2, Int, Int](f, shrink)
    }
  }

  law("dinaturality") {
    val observations = observe[T2, Int]
    val fs           = step[T2]
    val gs           = step[T2]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given (P[T2, Int] is Observable) = observe
      dinaturality[T2, Int, Int](f, g)
    }
  }

  law("doubleDagger") {
    val observations = observe[T2, Int]
    val ps           = step2[T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T2, Int] is Observable) = observe
      doubleDagger(p)
    }
  }

  law("uniformity") {
    val observations = observe[T2, Int]
    val fs           = step[T2]

    forAll(observations, fs) { (observe, f) =>
      given (P[T2, Int] is Observable) = observe
      val (h, inverse)                          = bijection
      val g = conway.strong.left[Int, Int, T2](profunctor.unit(inverse)) >>> f >>> profunctor.unit(h)
      uniformity(f, g, h)
    }
  }

  law("congruence") {
    val observations = observe[T2, Int]
    val ps           = step[T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T2, Int] is Observable) = observe
      congruence(p, variant(p))
    }
  }
}

// ==== 𝒫ᵒᵖ: the product column, by duality ====

class PartialOpIsConwayTest
    extends ConwaySpec("Partialᵒᵖ (loops read backwards)", PartialFixedPoints) {
  def step[A: Sample]: Gen[Int ~> Either[A, Int]]               = Descent.step[A].map(Partial.fromTotal(_))
  def step2[A: Sample]: Gen[Int ~> Either[Either[A, Int], Int]] = Descent.step2[A].map(Partial.fromTotal(_))
  def shrink: Int ~> Int                                        = Partial.fromTotal(_ / 2)

  def bijection: (Int ~> Int, Int ~> Int) = {
    (Partial.fromTotal(x => -x), Partial.fromTotal(x => -x))
  }
}
