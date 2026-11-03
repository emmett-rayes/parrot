package parrot
package category

import Category.Type

/** The laws of [[Strong]], for bistrong promonads over 𝒮: every strength in the library is bistrong. */
abstract class StrongSpec(
  name: String,
  tracked val strong: Strong.Bistrong { val profunctor: Promonad { val category: Category { type Obj = Type } } },
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
      val observations = observe[T[T3, T4], T[T3, T3]]
      val ps           = arrow[T1, T2]
      val fs           = category.arrow[T4, T1]
      val gs           = category.arrow[T2, T3]

      forAll(observations, ps, fs, gs) { (observe, p, f, g) =>
        given (P[T[T3, T4], T[T3, T3]] is Observable) = observe
        naturality[T1, T2, T4, T3, T3](p, f, g)
      }
    }

    law("dinaturality") {
      val observations = observe[T[T4, T1], T[T3, T2]]
      val ps           = arrow[T1, T2]
      val hs           = category.arrow[T4, T3]

      forAll(observations, ps, hs) { (observe, p, h) =>
        given (P[T[T4, T1], T[T3, T2]] is Observable) = observe
        dinaturality(p, h)
      }
    }

    law("unitality") {
      val observations = observe[T1, T2]
      val ps           = arrow[T1, T2]

      forAll(observations, ps) { (observe, p) =>
        given (P[T1, T2] is Observable) = observe
        unitality(p)
      }
    }

    law("associativity") {
      val observations = observe[T[T[T4, T3], T1], T[T[T4, T3], T2]]
      val ps           = arrow[T1, T2]

      forAll(observations, ps) { (observe, p) =>
        given (P[T[T[T4, T3], T1], T[T[T4, T3], T2]] is Observable) = observe
        associativity[T1, T2, T4, T3](p)
      }
    }

    law("leftCongruence") {
      val observations = observe[T[T4, T1], T[T4, T2]]
      val ps           = arrow[T1, T2]

      forAll(observations, ps) { (observe, p) =>
        given (P[T[T4, T1], T[T4, T2]] is Observable) = observe
        leftCongruence[T1, T2, T4](p, variant(p))
      }
    }
  }
}

/** The laws of [[Strong.Bistrong]], for bistrong promonads over 𝒮. */
abstract class BistrongSpec(
  name: String,
  tracked override val strong: Strong.Bistrong {
    val profunctor: Promonad { val category: Category { type Obj = Type } }
  },
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
    val observations = observe[(T4 * T1) * T3, (T4 * T2) * T3]
    val ps           = arrow[T1, T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[(T4 * T1) * T3, (T4 * T2) * T3] is Observable) = observe
      compatibility[T1, T2, T4, T3](p)
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
