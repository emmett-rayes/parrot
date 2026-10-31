package parrot
package category

import org.scalacheck.Gen

/** The laws of [[Freyd]] and of its [[Category]], for Freyd categories on promonads over 𝒮. */
abstract class FreydSpec(
  name: String,
  tracked val F: Freyd { val P: Promonad { val K: Category { type Obj = Type } } },
)(using
  promonad: PromonadFixture.On[F.P.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[F.S.M.Tensor[X, Y]],
) extends LawSuite("Freyd", name) {
  import types.{T1, T2, T3, T4, given}
  import promonad.*
  import F.{-->, >>>}
  import F.S.M.`*`
  import F.FreydLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[X * Y] = tensor[X, Y]

  law("unit") {
    val observations = observe[T1 * T4, T2 * T4]
    val fs           = base.arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given (((T1 * T4) --> (T2 * T4)) is Observable) = observe
      unit[T1, T2, T4](f)
    }
  }

  law("multiply") {
    val observations = observe[T1 * T4, T3 * T4]
    val ps           = arrow[T1, T2]
    val qs           = arrow[T2, T3]

    forAll(observations, ps, qs) { (observe, p, q) =>
      given (((T1 * T4) --> (T3 * T4)) is Observable) = observe
      multiply[T1, T2, T3, T4](p, q)
    }
  }

  law("centrality") {
    val observations = observe[T1 * T4, T2 * T3]
    val fs           = base.arrow[T1, T2]
    val qs           = arrow[T4, T3]

    forAll(observations, fs, qs) { (observe, f, q) =>
      given (((T1 * T4) --> (T2 * T3)) is Observable) = observe
      centrality(f, q)
    }
  }

  also("Category") {
    import F.CategoryLaws.*

    law("leftIdentity") {
      val observations = observe[T1, T2]
      val ps           = arrow[T1, T2]

      forAll(observations, ps) { (observe, p) =>
        given ((T1 --> T2) is Observable) = observe
        leftIdentity(p)
      }
    }

    law("rightIdentity") {
      val observations = observe[T1, T2]
      val ps           = arrow[T1, T2]

      forAll(observations, ps) { (observe, p) =>
        given ((T1 --> T2) is Observable) = observe
        rightIdentity(p)
      }
    }

    law("associativity") {
      val observations = observe[T1, T4]
      val ps           = arrow[T1, T2]
      val qs           = arrow[T2, T3]
      val rs           = arrow[T3, T4]

      forAll(observations, ps, qs, rs) { (observe, p, q, r) =>
        given ((T1 --> T4) is Observable) = observe
        associativity(p, q, r)
      }
    }

    law("congruence") {
      val observations = observe[T1, T3]
      val ps           = arrow[T1, T2]
      val qs           = arrow[T2, T3]

      forAll(observations, ps, qs) { (observe, p, q) =>
        given ((T1 --> T3) is Observable) = observe
        congruence(p, variant(p), q, variant(q))
      }
    }
  }

  /** Interchange: running *p* and *q* side by side in either order gives the same result. It holds when the effect is
    * commutative and fails otherwise; it is not a law of Freyd categories.
    */
  protected def interchange: Gen[Boolean] = {
    for {
      observe <- observe[T1 * T4, T2 * T3]
      p       <- arrow[T1, T2]
      q       <- arrow[T4, T3]
    } yield {
      given (((T1 * T4) --> (T2 * T3)) is Observable) = observe
      (F.first[T1, T2, T4](p) >>> F.second[T4, T3, T2](q)) =?= (F.second[T4, T3, T1](q) >>> F.first[T1, T2, T3](p))
    }
  }
}

class OptionKleisliProductIsFreydTest
    extends FreydSpec("Kleisli[Option] on Product", Freyd(Kleisli.OptionKleisli, Kleisli.OptionProduct)) {
  law("interchange", "holds: Option is a commutative monad") {
    forAll(interchange)(holds => holds)
  }
}

class OptionKleisliCoproductIsFreydTest
    extends FreydSpec("Kleisli[Option] on Coproduct", Freyd(Kleisli.OptionKleisli, Kleisli.OptionCoproduct)) {
  law("interchange", "holds: only one side runs") {
    forAll(interchange)(holds => holds)
  }
}

class StringWriterKleisliProductIsFreydTest
    extends FreydSpec("Kleisli[Writer[String]] on Product", Freyd(StringWriterKleisli, StringWriterProduct)) {
  counterexample("interchange", "logs are not commutative") {
    forAll(interchange)(holds => holds)
  }
}

class StringWriterKleisliCoproductIsFreydTest
    extends FreydSpec("Kleisli[Writer[String]] on Coproduct", Freyd(StringWriterKleisli, StringWriterCoproduct)) {
  law("interchange", "holds: only one side runs") {
    forAll(interchange)(holds => holds)
  }
}
