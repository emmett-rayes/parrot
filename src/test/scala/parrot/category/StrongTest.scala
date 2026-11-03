package parrot
package category

import Category.Type

/** The laws of [[Strong]], for bistrong promonads over 𝒮: every strength in the library is bistrong. */
abstract class StrongSpec(
  name: String,
  tracked val strong: Strong.Bistrong.On[Promonad.On[Category { type Obj = Type }]],
  structure: String = "Strong",
)(using
  promonad: PromonadFixture.For[strong.profunctor.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[strong.monoidal.Tensor[X, Y]],
) extends LawSuite(structure, name) {
  import types.{T1, T2, T3, T4, given}
  import promonad.*
  import strong.profunctor.P
  import strong.StrongLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[strong.monoidal.Tensor[X, Y]] = tensor[X, Y]

  private type T[X, Y] = strong.monoidal.Tensor[X, Y]

  also("Strong") {
    law("naturality") {
      val observations = onArrows[T1, T2, T[T3, T4], T[T3, T3]]
      val fs           = category.arrow[T4, T1]
      val gs           = category.arrow[T2, T3]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((P[T1, T2] -> P[T[T3, T4], T[T3, T3]]) is Observable) = observe
        naturality[T1, T2, T4, T3, T3](f, g)
      }
    }

    law("dinaturality") {
      val observations = onArrows[T1, T2, T[T4, T1], T[T3, T2]]
      val hs           = category.arrow[T4, T3]

      forAll(observations, hs) { (observe, h) =>
        given ((P[T1, T2] -> P[T[T4, T1], T[T3, T2]]) is Observable) = observe
        dinaturality[T1, T2, T4, T3](h)
      }
    }

    law("unitality") {
      val observations = onArrows[T1, T2, T1, T2]

      forAll(observations) { observe =>
        given ((P[T1, T2] -> P[T1, T2]) is Observable) = observe
        unitality[T1, T2]
      }
    }

    law("associativity") {
      val observations = onArrows[T1, T2, T[T[T4, T3], T1], T[T[T4, T3], T2]]

      forAll(observations) { observe =>
        given ((P[T1, T2] -> P[T[T[T4, T3], T1], T[T[T4, T3], T2]]) is Observable) = observe
        associativity[T1, T2, T4, T3]
      }
    }
  }
}

/** The laws of [[Strong.Bistrong]], for bistrong promonads over 𝒮. */
abstract class BistrongSpec(
  name: String,
  tracked override val strong: Strong.Bistrong.On[Promonad.On[Category { type Obj = Type }]],
)(using
  promonad: PromonadFixture.For[strong.profunctor.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[strong.monoidal.Tensor[X, Y]],
) extends StrongSpec(name, strong, "Bistrong") {
  import types.{T1, T2, T3, T4, given}
  import promonad.*
  import strong.profunctor.P
  import strong.monoidal.`*`
  import strong.BistrongLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[X * Y] = tensor[X, Y]

  law("compatibility") {
    val observations = onArrows[T1, T2, (T4 * T1) * T3, (T4 * T2) * T3]

    forAll(observations) { observe =>
      given ((P[T1, T2] -> P[(T4 * T1) * T3, (T4 * T2) * T3]) is Observable) = observe
      compatibility[T1, T2, T4, T3]
    }
  }
}

class OptionKleisliProductIsBistrongTest
    extends BistrongSpec("Kleisli[Option] on Product", Kleisli.OptionProduct)

class OptionKleisliCoproductIsBistrongTest
    extends BistrongSpec("Kleisli[Option] on Coproduct", Kleisli.OptionCoproduct)

/** The string writer's arrows, run side by side on pairs. */
object StringWriterProduct extends Kleisli.ProductStrength(StringWriterKleisli)

/** The string writer's arrows, run on one side of a tagged union. */
object StringWriterCoproduct extends Kleisli.CoproductStrength(StringWriterKleisli)

class StringWriterKleisliProductIsBistrongTest
    extends BistrongSpec("Kleisli[Writer[String]] on Product", StringWriterProduct)

class StringWriterKleisliCoproductIsBistrongTest
    extends BistrongSpec("Kleisli[Writer[String]] on Coproduct", StringWriterCoproduct)
