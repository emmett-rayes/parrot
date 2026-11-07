package parrot
package category

import Category.Type

/** The laws of [[Bistrong]], for bistrong promonads over 𝒮. */
abstract class BistrongSpec(
  name: String,
  tracked override val strong: Bistrong.On[Promonad.On[Category { type Obj = Type }]],
)(using
  promonad: PromonadFixture.For[strong.profunctor.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[strong.monoidal.Tensor[X, Y]],
) extends StrongSpec(name, strong, "Bistrong") {
  import types.{T1, T2, T3, given}
  import promonad.*
  import strong.profunctor.P
  import strong.monoidal.`*`
  import strong.BistrongLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[X * Y] = tensor[X, Y]

  law("braiding") {
    val observations = onArrows[T1, T2, T1 * T3, T2 * T3]

    forAll(observations) { observe =>
      given ((P[T1, T2] -> P[T1 * T3, T2 * T3]) is Observable) = observe
      braiding[T1, T2, T3]
    }
  }
}

class OptionKleisliProductIsBistrongTest
    extends BistrongSpec("Kleisli[Option] on Product", Kleisli.OptionProduct)

class OptionKleisliCoproductIsBistrongTest
    extends BistrongSpec("Kleisli[Option] on Coproduct", Kleisli.OptionCoproduct)

class TotalParallelIsBistrongTest   extends BistrongSpec("Total on Product", Total.Parallel)
class TotalChoiceIsBistrongTest     extends BistrongSpec("Total on Coproduct", Total.Choice)
class PartialParallelIsBistrongTest extends BistrongSpec("Partial on Product", Partial.Parallel)
class PartialChoiceIsBistrongTest   extends BistrongSpec("Partial on Coproduct", Partial.Choice)

class PartialComputationsProductIsBistrongTest
    extends BistrongSpec("Computations on Product", Partial.ComputationsProduct)

class PartialComputationsCoproductIsBistrongTest
    extends BistrongSpec("Computations on Coproduct", Partial.ComputationsCoproduct)

/** The string writer's arrows, run side by side on pairs. */
object StringWriterProduct extends Kleisli.ProductStrength(StringWriterKleisli)

/** The string writer's arrows, run on one side of a tagged union. */
object StringWriterCoproduct extends Kleisli.CoproductStrength(StringWriterKleisli, Total.Coproducts)

class StringWriterKleisliProductIsBistrongTest
    extends BistrongSpec("Kleisli[Writer[String]] on Product", StringWriterProduct)

class StringWriterKleisliCoproductIsBistrongTest
    extends BistrongSpec("Kleisli[Writer[String]] on Coproduct", StringWriterCoproduct)
