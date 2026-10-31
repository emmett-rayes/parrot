package parrot
package category

/** The laws of [[Strong]] and [[Strong.Bistrong]], for bistrong promonads over 𝒮. */
abstract class StrongSpec(
  name: String,
  tracked val S: Strong.Bistrong { val P: Promonad { val K: Category { type Obj = Type } } },
)(using
  promonad: PromonadFixture.On[S.P.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[S.M.Tensor[X, Y]],
) extends LawSuite("Strong", name) {
  import types.{T1, T2, T3, T4, given}
  import promonad.*
  import S.P
  import P.P
  import S.StrongLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[S.M.Tensor[X, Y]] = tensor[X, Y]

  private type T[X, Y] = S.M.Tensor[X, Y]

  law("naturality") {
    val observations = observe[T[T3, T4], T[T3, T3]]
    val ps           = arrow[T1, T2]
    val fs           = base.arrow[T4, T1]
    val gs           = base.arrow[T2, T3]

    forAll(observations, ps, fs, gs) { (observe, p, f, g) =>
      given (P[T[T3, T4], T[T3, T3]] is Observable) = observe
      naturality[T1, T2, T4, T3, T3](p, f, g)
    }
  }

  law("dinaturality") {
    val observations = observe[T[T4, T1], T[T3, T2]]
    val ps           = arrow[T1, T2]
    val hs           = base.arrow[T4, T3]

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

  also("Bistrong") {
    import S.BistrongLaws.*

    law("compatibility") {
      val observations = observe[T[T[T4, T1], T3], T[T[T4, T2], T3]]
      val ps           = arrow[T1, T2]

      forAll(observations, ps) { (observe, p) =>
        given (P[T[T[T4, T1], T3], T[T[T4, T2], T3]] is Observable) = observe
        compatibility[T1, T2, T4, T3](p)
      }
    }
  }
}

class OptionKleisliProductIsStrongTest
    extends StrongSpec("Kleisli[Option] on Product", Kleisli.OptionProduct)

class OptionKleisliCoproductIsStrongTest
    extends StrongSpec("Kleisli[Option] on Coproduct", Kleisli.OptionCoproduct)

/** The string writer's arrows, run side by side on pairs. */
object StringWriterProduct extends Kleisli.ProductStrength(StringWriterKleisli)

/** The string writer's arrows, run on one side of a tagged union. */
object StringWriterCoproduct extends Kleisli.CoproductStrength(StringWriterKleisli)

class StringWriterKleisliProductIsStrongTest
    extends StrongSpec("Kleisli[Writer[String]] on Product", StringWriterProduct)

class StringWriterKleisliCoproductIsStrongTest
    extends StrongSpec("Kleisli[Writer[String]] on Coproduct", StringWriterCoproduct)
