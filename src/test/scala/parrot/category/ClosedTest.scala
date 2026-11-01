package parrot
package category

import org.scalacheck.Gen

import Sample.given
import Category.Type

/** The laws of [[Closed]], for closed structures on a category whose objects are all types.
  *
  * An arrow into an internal hom is observed by evaluation, through its uncurried form, and an arrow between internal
  * homs at sample elements of the first, curried from generated arrows.
  */
abstract class ClosedSpec(tracked val C: Closed { val M: Monoidal { val K: Category { type Obj = Type } } })(using
  category: CategoryFixture.On[C.M.K.type],
  typename: TypeName[C.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[C.M.Tensor[X, Y]],
  unit: Sample[C.M.I],
) extends LawSuite("Closed", s"${typename.name} on ${category.name}") {
  import types.{T1, T2, T3, T4, given}
  import category.*
  import C.M.{I, `*`}
  import C.M.K.{-->, >>>}
  import C.`^`
  import C.ClosedLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[X * Y] = tensor[X, Y]

  /** Observes arrows *X* → (*Y* ⇒ *Z*) through their uncurried forms *X* ⊗ *Y* → *Z*. */
  private def curried[X: Sample, Y: Sample, Z: Sample]: Gen[(X --> (Z `^` Y)) is Observable] = {
    observe[X * Y, Z].map { observe =>
      Observable.through[X --> (Z `^` Y), (X * Y) --> Z](List(g => C.uncurry[Y, Z, X](g)))(using observe)
    }
  }

  /** Observes arrows (*A*₁ ⇒ *B*₁) → (*A*₂ ⇒ *B*₂) at sample elements *I* → (*A*₁ ⇒ *B*₁). */
  private def onHoms[A1: Sample, B1: Sample, A2: Sample, B2: Sample]
    : Gen[((B1 `^` A1) --> (B2 `^` A2)) is Observable] = {
    for {
      elements <- Gen.listOfN(4, arrow[I * A1, B1].map((f: (I * A1) --> B1) => C.curry[A1, B1, I](f)))
      observe  <- curried[I, A2, B2]
    } yield Observable.through[(B1 `^` A1) --> (B2 `^` A2), I --> (B2 `^` A2)](elements.map(e => m => e >>> m))(
      using observe
    )
  }

  law("beta") {
    val observations = observe[T1 * T2, T4]
    val fs           = arrow[T1 * T2, T4]

    forAll(observations, fs) { (observe, f) =>
      given (((T1 * T2) --> T4) is Observable) = observe
      beta[T2, T4, T1](f)
    }
  }

  law("eta") {
    val observations = curried[T1, T2, T4]
    val gs           = arrow[T1 * T2, T4].map((f: (T1 * T2) --> T4) => C.curry[T2, T4, T1](f))

    forAll(observations, gs) { (observe, g) =>
      given ((T1 --> (T4 `^` T2)) is Observable) = observe
      eta[T2, T4, T1](g)
    }
  }

  law("curryCongruence") {
    val observations = curried[T1, T2, T4]
    val fs           = arrow[T1 * T2, T4]

    forAll(observations, fs) { (observe, f) =>
      given ((T1 --> (T4 `^` T2)) is Observable) = observe
      curryCongruence[T2, T4, T1](f, variant(f))
    }
  }

  also("Profunctor") {
    import C.internalHom.BifunctorLaws.*

    law("identity") {
      forAll(onHoms[T1, T2, T1, T2]) { observe =>
        given (((T2 `^` T1) --> (T2 `^` T1)) is Observable) = observe
        identity[T1, T2]
      }
    }

    law("composition") {
      forAll(
        onHoms[T1, T2, T4, T3],
        Gen.zip(arrow[T3, T1], arrow[T2, T1]),
        Gen.zip(arrow[T4, T3], arrow[T1, T3]),
      ) { case (observe, (f1, g1), (f2, g2)) =>
        given (((T2 `^` T1) --> (T3 `^` T4)) is Observable) = observe
        composition[T1, T2, T3, T1, T4, T3](f1, g1, f2, g2)
      }
    }

    law("congruence") {
      val fs = arrow[T4, T1]
      val gs = arrow[T2, T3]

      forAll(onHoms[T1, T2, T4, T3], fs, gs) { (observe, f, g) =>
        given (((T2 `^` T1) --> (T3 `^` T4)) is Observable) = observe
        congruence[T1, T2, T4, T3](f, variant(f), g, variant(g))
      }
    }
  }
}

class ScalaExponentialIsClosedTest extends ClosedSpec(Total.Exponentials)
