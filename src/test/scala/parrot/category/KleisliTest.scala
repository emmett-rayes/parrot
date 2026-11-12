package parrot
package category

import Sample.given
import Category.Type

/** The laws of [[Kleisli.ClassicalOf]]: those of [[Classical]], and the derived operations of the classical monad. */
abstract class ClassicalOfSpec(
  name: String,
  tracked override val restriction: Kleisli.ClassicalOf,
  tracked override val functor: Functor.Into[restriction.category.type] {
    val source: Category { type Obj = Type }; type Self[A] = A
  },
  structure: String = "ClassicalOf",
)(using
  category: CategoryFixture.For[restriction.category.type],
  source: CategoryFixture.For[functor.source.type],
  types: SampleTypes,
) extends ClassicalSpec(name, restriction, functor, structure) {
  import types.{T1, T2, given}
  import category.*
  import restriction.promonad.monad.M
  import restriction.ClassicalOfLaws.*

  also("ClassicalOf") {
    law("attemptDefinition") {
      val observations = observe[T1, Option[T2]]
      val ps           = arrow[T1, T2]

      forAll(observations, ps) { (observe, p) =>
        given ((T1 -> M[Option[T2]]) is Observable) = observe
        attemptDefinition(p)
      }
    }
  }
}

class OptionKleisliIsClassicalOfTest
    extends ClassicalOfSpec("Kleisli[Option]", Kleisli.OptionDomains, Kleisli.OptionKleisli.pure)

class StringStateIsClassicalOfTest
    extends ClassicalOfSpec("Kleisli[State[String, Option]]", StringStateDomains, StringStateKleisli.pure)

/** The laws of [[Kleisli.CocartesianOf]]: those of [[Cocartesian]], and the strength over coproducts as a coproduct of
  * arrows.
  */
abstract class CocartesianOfSpec(
  tracked override val premonoidal: Kleisli.CocartesianOf { val promonad: Kleisli.Of[Monad.On[Total.type]] },
  structure: String = "CocartesianOf",
)(using
  category: CategoryFixture.For[premonoidal.category.type],
  typename: TypeName[premonoidal.type],
  types: SampleTypes,
  tensor: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[premonoidal.Tensor[X, Y]],
  unit: Sample[premonoidal.I],
) extends CocartesianSpec(premonoidal, structure) {
  import types.{T1, T2, T3, given}
  import category.*
  import premonoidal.+
  import premonoidal.promonad.P
  import premonoidal.CocartesianOfLaws.*

  private given TensorSample: [X: Sample, Y: Sample] => Sample[premonoidal.Tensor[X, Y]] = tensor[X, Y]

  also("CocartesianOf") {
    law("strengthIsCoproduct") {
      val observations = observe[T3 + T1, T3 + T2]
      val ps           = arrow[T1, T2]

      forAll(observations, ps) { (observe, p) =>
        given (P[T3 + T1, T3 + T2] is Observable) = observe
        strengthIsCoproduct[T1, T2, T3](p)
      }
    }
  }
}

/** Functions that write a log have the coproducts of 𝒮, although their effects do not commute. */
object StringWriterCoproducts extends Kleisli.CocartesianOf(StringWriterKleisli, Total.Coproducts)

class OptionKleisliIsCocartesianOfTest       extends CocartesianOfSpec(Kleisli.OptionCoproducts)
class StringWriterKleisliIsCocartesianOfTest extends CocartesianOfSpec(StringWriterCoproducts)
