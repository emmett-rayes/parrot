package parrot
package category

import org.scalacheck.Gen

import Sample.given
import Category.Type

/** The laws of [[Elgot]]: those of [[GuardedIteration]], with steps whose loops stop. */
abstract class ElgotSpec(
  name: String,
  tracked override val iteration: Elgot.On[Bistrong.On[Promonad.On[Category { type Obj = Type }]]],
  structure: String = "Elgot",
)(using
  promonad: PromonadFixture.For[iteration.strong.profunctor.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[iteration.strong.monoidal.Tensor[X, Y]],
) extends GuardedIterationSpec(name, iteration, structure)

// ==== 𝒫 ====

class PartialLoopsIsElgotTest extends ElgotSpec("Partial (while loops)", Partial.Loops) {
  def step[A: Sample]: Gen[Int ~> Either[A, Int]]               = Descent.step[A].map(Partial.fromTotal(_))
  def step2[A: Sample]: Gen[Int ~> Either[Either[A, Int], Int]] = Descent.step2[A].map(Partial.fromTotal(_))
  def shrink: Int ~> Int                                        = Partial.fromTotal(_ / 2)

  def bijection: (Int ~> Int, Int ~> Int) = {
    (Partial.fromTotal(x => -x), Partial.fromTotal(x => -x))
  }
}

/** Iteration recovered from the trace of [[Partial.Loops]]: the bridge back. */
object PartialLoopsFromFeedback extends Elgot.OfTraced(Partial.Feedback)

class PartialFeedbackIsElgotTest
    extends ElgotSpec("Partial (iteration of the trace)", PartialLoopsFromFeedback) {
  def step[A: Sample]: Gen[Int ~> Either[A, Int]]               = Descent.step[A].map(Partial.fromTotal(_))
  def step2[A: Sample]: Gen[Int ~> Either[Either[A, Int], Int]] = Descent.step2[A].map(Partial.fromTotal(_))
  def shrink: Int ~> Int                                        = Partial.fromTotal(_ / 2)

  def bijection: (Int ~> Int, Int ~> Int) = {
    (Partial.fromTotal(x => -x), Partial.fromTotal(x => -x))
  }
}
