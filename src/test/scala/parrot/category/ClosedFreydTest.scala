package parrot
package category

import org.scalacheck.Gen

import Category.Type

/** The laws of [[ClosedFreyd]], for closed structures on bistrong promonads over a category whose objects are all
  * types.
  *
  * A pure morphism into a Kleisli exponential is observed by evaluation, through its uncurried form.
  */
abstract class ClosedFreydSpec(
  name: String,
  tracked val closed: ClosedFreyd.On[Bistrong.On[Promonad.On[Category { type Obj = Type }]]],
)(using
  promonad: PromonadFixture.For[closed.strong.profunctor.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[closed.strong.monoidal.Tensor[X, Y]],
) extends LawSuite("ClosedFreyd", name) {
  import types.{T1, T2, T4, given}
  import promonad.*
  import closed.strong.monoidal.`*`
  import closed.strong.profunctor.arrows.-->
  import closed.strong.profunctor.category.--> as ==>
  import closed.`^`
  import closed.ClosedFreydLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[X * Y] = tensor[X, Y]

  /** Observes pure morphisms *X* → (*Y* ⇒ *Z*) through their uncurried forms *P*(*X* ⊗ *Y*,*Z*). */
  private def curried[X: Sample, Y: Sample, Z: Sample]: Gen[(X ==> (Z `^` Y)) is Observable] = {
    observe[X * Y, Z].map { observe =>
      Observable.through[X ==> (Z `^` Y), (X * Y) --> Z](List(g => closed.uncurry[Y, Z, X](g)))(using observe)
    }
  }

  law("beta") {
    val observations = observe[T1 * T2, T4]
    val ps           = arrow[T1 * T2, T4]

    forAll(observations, ps) { (observe, p) =>
      given (((T1 * T2) --> T4) is Observable) = observe
      beta[T2, T4, T1](p)
    }
  }

  law("eta") {
    val observations = curried[T1, T2, T4]
    val gs           = arrow[T1 * T2, T4].map((p: (T1 * T2) --> T4) => closed.curry[T2, T4, T1](p))

    forAll(observations, gs) { (observe, g) =>
      given ((T1 ==> (T4 `^` T2)) is Observable) = observe
      eta[T2, T4, T1](g)
    }
  }

  law("curryCongruence") {
    val observations = curried[T1, T2, T4]
    val ps           = arrow[T1 * T2, T4]

    forAll(observations, ps) { (observe, p) =>
      given ((T1 ==> (T4 `^` T2)) is Observable) = observe
      curryCongruence[T2, T4, T1](p, variant(p))
    }
  }

  law("uncurryIsEval") {
    val observations = observe[T1 * T2, T4]
    val gs           = arrow[T1 * T2, T4].map((p: (T1 * T2) --> T4) => closed.curry[T2, T4, T1](p))

    forAll(observations, gs) { (observe, g) =>
      given (((T1 * T2) --> T4) is Observable) = observe
      uncurryIsEval[T2, T4, T1](g)
    }
  }
}

/** The Kleisli exponentials of `Kleisli[Option]`: functions that may fail. */
object OptionKleisliExponentials extends Kleisli.ClosedFreydOf(Kleisli.OptionProduct)

/** The Kleisli exponentials of `Kleisli[Writer[String]]`: functions that log. */
object StringWriterKleisliExponentials extends Kleisli.ClosedFreydOf(StringWriterProduct)

class PartialExponentialsIsClosedFreydTest
    extends ClosedFreydSpec("Computations on Product", Partial.Exponentials)

class OptionKleisliExponentialsIsClosedFreydTest
    extends ClosedFreydSpec("Kleisli[Option] on Product", OptionKleisliExponentials)

class StringWriterKleisliExponentialsIsClosedFreydTest
    extends ClosedFreydSpec("Kleisli[Writer[String]] on Product", StringWriterKleisliExponentials)
