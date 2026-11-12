package parrot
package category

import org.scalacheck.Gen

import Category.Type

/** The laws of [[Freyd]], for Freyd categories on promonads over 𝒮. */
abstract class FreydSpec(
  name: String,
  tracked override val premonoidal: Freyd.On[Bistrong.On[Promonad.On[Category { type Obj = Type }]]],
)(using
  promonad: PromonadFixture.For[premonoidal.strong.profunctor.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[premonoidal.Tensor[X, Y]],
  unitSample: Sample[premonoidal.I],
) extends SymmetricPremonoidalSpec(name, premonoidal, "Freyd")(using promonad.arrows, types, tensor, unitSample) {
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

  also("BinoidalFunctor") {
    import premonoidal.tensor.BinoidalFunctorLaws.lmapComposition

    law("lmapComposition", "of the tensor: the right strength respects composition") {
      val observations = observe[T1 * T4, T3 * T4]
      val ps           = arrow[T1, T2]
      val qs           = arrow[T2, T3]

      forAll(observations, ps, qs) { (observe, p, q) =>
        given (((T1 * T4) --> (T3 * T4)) is Observable) = observe
        lmapComposition[T1, T2, T3, T4](p, q)
      }
    }
  }

  law("leftToRightIsStrengths") {
    val observations = observe[T1 * T4, T2 * T3]
    val ps           = arrow[T1, T2]
    val qs           = arrow[T4, T3]

    forAll(observations, ps, qs) { (observe, p, q) =>
      given (((T1 * T4) --> (T2 * T3)) is Observable) = observe
      leftToRightIsStrengths(p, q)
    }
  }

  law("rightToLeftIsStrengths") {
    val observations = observe[T1 * T4, T2 * T3]
    val ps           = arrow[T1, T2]
    val qs           = arrow[T4, T3]

    forAll(observations, ps, qs) { (observe, p, q) =>
      given (((T1 * T4) --> (T2 * T3)) is Observable) = observe
      rightToLeftIsStrengths(p, q)
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
    extends FreydSpec("Kleisli[Option] on Product", Freyd(Kleisli.OptionProduct)) {
  law("interchange", "holds: Option is a commutative monad") {
    forAll(interchange)(holds => holds)
  }
}

class OptionKleisliCoproductIsFreydTest
    extends FreydSpec("Kleisli[Option] on Coproduct", Freyd(Kleisli.OptionCoproduct)) {
  law("interchange", "holds: only one side runs") {
    forAll(interchange)(holds => holds)
  }
}

class StringWriterKleisliProductIsFreydTest
    extends FreydSpec("Kleisli[Writer[String]] on Product", Freyd(StringWriterProduct)) {
  counterexample("interchange", "logs are not commutative") {
    forAll(interchange)(holds => holds)
  }
}

class StringWriterKleisliCoproductIsFreydTest
    extends FreydSpec("Kleisli[Writer[String]] on Coproduct", Freyd(StringWriterCoproduct)) {
  law("interchange", "holds: only one side runs") {
    forAll(interchange)(holds => holds)
  }
}

class TotalParallelIsFreydTest extends FreydSpec("Total on Product", Freyd(Total.Parallel)) {
  law("interchange", "holds: functions have no effects") {
    forAll(interchange)(holds => holds)
  }
}

class TotalChoiceIsFreydTest extends FreydSpec("Total on Coproduct", Freyd(Total.Choice)) {
  law("interchange", "holds: only one side runs") {
    forAll(interchange)(holds => holds)
  }
}

class PartialParallelIsFreydTest extends FreydSpec("Partial on Product", Freyd(Partial.Parallel)) {
  law("interchange", "holds: programs diverge in either order if one side does") {
    forAll(interchange)(holds => holds)
  }
}

class PartialChoiceIsFreydTest extends FreydSpec("Partial on Coproduct", Freyd(Partial.Choice)) {
  law("interchange", "holds: only one side runs") {
    forAll(interchange)(holds => holds)
  }
}

class PartialComputationsProductIsFreydTest
    extends FreydSpec("Computations on Product", Freyd(Partial.ComputationsProduct)) {
  law("interchange", "holds: programs diverge in either order if one side does") {
    forAll(interchange)(holds => holds)
  }
}

class PartialComputationsCoproductIsFreydTest
    extends FreydSpec("Computations on Coproduct", Freyd(Partial.ComputationsCoproduct)) {
  law("interchange", "holds: only one side runs") {
    forAll(interchange)(holds => holds)
  }
}

/** A class below [[Freyd]] that mixes the symmetry in again: the mixin has [[Premonoidal]] as its self-type and
  * restates none of its parameters, so it applies wherever the class is.
  */
class MixedAgain(tracked override val strong: StrongPromonad) extends Freyd(strong), SymmetricPremonoidal

class MixedAgainIsFreydTest extends FreydSpec("Option on Product (mixed in again)", MixedAgain(Kleisli.OptionProduct))
