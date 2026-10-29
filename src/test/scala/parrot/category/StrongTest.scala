package parrot
package category

import org.scalacheck.Gen

/** The laws of [[Strong]] and [[Freyd]], for strong promonads over 𝒮. */
abstract class StrongSpec(
  name: String,
  tracked val S: Strong { val P: Promonad { val K: Category { type Obj = Type } } },
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

  private lazy val F = Freyd(S)

  law("naturality") {
    val observations = observe[T[T4, T3], T[T3, T3]]
    val ps           = arrow[T1, T2]
    val fs           = base.arrow[T4, T1]
    val gs           = base.arrow[T2, T3]

    forAll(observations, ps, fs, gs) { (observe, p, f, g) =>
      given (P[T[T4, T3], T[T3, T3]] is Observable) = observe
      naturality[T1, T2, T4, T3, T3](p, f, g)
    }
  }

  law("dinaturality") {
    val observations = observe[T[T1, T4], T[T2, T3]]
    val ps           = arrow[T1, T2]
    val hs           = base.arrow[T4, T3]

    forAll(observations, ps, hs) { (observe, p, h) =>
      given (P[T[T1, T4], T[T2, T3]] is Observable) = observe
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
    val observations = observe[T[T1, T[T4, T3]], T[T2, T[T4, T3]]]
    val ps           = arrow[T1, T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T[T1, T[T4, T3]], T[T2, T[T4, T3]]] is Observable) = observe
      associativity[T1, T2, T4, T3](p)
    }
  }

  law("secondByBraiding") {
    val observations = observe[T[T4, T1], T[T4, T2]]
    val ps           = arrow[T1, T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T[T4, T1], T[T4, T2]] is Observable) = observe
      secondByBraiding[T1, T2, T4](p)
    }
  }

  law("firstCongruence") {
    val observations = observe[T[T1, T4], T[T2, T4]]
    val ps           = arrow[T1, T2]

    forAll(observations, ps) { (observe, p) =>
      given (P[T[T1, T4], T[T2, T4]] is Observable) = observe
      firstCongruence[T1, T2, T4](p, variant(p))
    }
  }

  also("Freyd") {
    import F.FreydLaws.*

    law("unit") {
      val observations = observe[T[T1, T4], T[T2, T4]]
      val fs           = base.arrow[T1, T2]

      forAll(observations, fs) { (observe, f) =>
        given (P[T[T1, T4], T[T2, T4]] is Observable) = observe
        unit[T1, T2, T4](f)
      }
    }

    law("multiply") {
      val observations = observe[T[T1, T4], T[T3, T4]]
      val ps           = arrow[T1, T2]
      val qs           = arrow[T2, T3]

      forAll(observations, ps, qs) { (observe, p, q) =>
        given (P[T[T1, T4], T[T3, T4]] is Observable) = observe
        multiply[T1, T2, T3, T4](p, q)
      }
    }

    law("centrality") {
      val observations = observe[T[T1, T4], T[T2, T3]]
      val fs           = base.arrow[T1, T2]
      val qs           = arrow[T4, T3]

      forAll(observations, fs, qs) { (observe, f, q) =>
        given (P[T[T1, T4], T[T2, T3]] is Observable) = observe
        centrality(f, q)
      }
    }
  }

  /** Interchange: running *p* and *q* side by side in either order gives the same result. It holds when the effect is
    * commutative and fails otherwise; it is not a law of Freyd categories.
    */
  protected def interchange: Gen[Boolean] = {
    for {
      observe <- observe[T[T1, T4], T[T2, T3]]
      p       <- arrow[T1, T2]
      q       <- arrow[T4, T3]
    } yield {
      given (P[T[T1, T4], T[T2, T3]] is Observable) = observe
      P.multiply(S.second[T4, T3, T2](q), S.first[T1, T2, T4](p)) =?=
        P.multiply(S.first[T1, T2, T3](p), S.second[T4, T3, T1](q))
    }
  }
}

class OptionKleisliProductIsStrongTest
    extends StrongSpec("Kleisli[Option] on Product", Kleisli.OptionProduct) {
  also("Freyd") {
    law("interchange", "holds: Option is a commutative monad") {
      forAll(interchange)(holds => holds)
    }
  }
}

class OptionKleisliCoproductIsStrongTest
    extends StrongSpec("Kleisli[Option] on Coproduct", Kleisli.OptionCoproduct) {
  also("Freyd") {
    law("interchange", "holds: only one side runs") {
      forAll(interchange)(holds => holds)
    }
  }
}

/** The string writer's arrows, run side by side on pairs. */
object StringWriterProduct extends Kleisli.ProductStrength(StringWriterKleisli)

/** The string writer's arrows, run on one side of a tagged union. */
object StringWriterCoproduct extends Kleisli.CoproductStrength(StringWriterKleisli)

class StringWriterKleisliProductIsStrongTest
    extends StrongSpec("Kleisli[Writer[String]] on Product", StringWriterProduct) {
  also("Freyd") {
    counterexample("interchange", "logs are not commutative") {
      forAll(interchange)(holds => holds)
    }
  }
}

class StringWriterKleisliCoproductIsStrongTest
    extends StrongSpec("Kleisli[Writer[String]] on Coproduct", StringWriterCoproduct) {
  also("Freyd") {
    law("interchange", "holds: only one side runs") {
      forAll(interchange)(holds => holds)
    }
  }
}
