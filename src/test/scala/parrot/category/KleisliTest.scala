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
