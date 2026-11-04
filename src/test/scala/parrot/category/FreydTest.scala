package parrot
package category

import org.scalacheck.Gen

import Category.Type

/** The laws of [[Freyd]], for Freyd categories on promonads over 𝒮. */
abstract class FreydSpec(
  name: String,
  tracked override val premonoidal: Freyd.On[Promonad.On[Category { type Obj = Type }]],
)(using
  promonad: PromonadFixture.For[premonoidal.promonad.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[premonoidal.Tensor[X, Y]],
  unitSample: Sample[premonoidal.I],
) extends PremonoidalSpec(name, premonoidal, "Freyd")(using promonad.arrows, types, tensor, unitSample) {
  import types.{T1, T2, T3, T4, given}
  import promonad.*
  import premonoidal.category.-->
  import premonoidal.`*`
  import premonoidal.FreydLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[X * Y] = tensor[X, Y]

  law("unit") {
    val observations = observe[T1 * T4, T2 * T4]
    val fs           = category.arrow[T1, T2]

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
      premonoidal.leftToRight(p, q) =?= premonoidal.rightToLeft(p, q)
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
