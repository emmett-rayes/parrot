package parrot
package category

import org.scalacheck.Gen

import Category.Type

/** The laws of [[Bifunctor]], for bifunctors **C** × **C** → **C** on a category whose objects are all types. */
abstract class BifunctorSpec(
  tracked override val category: Category { type Obj = Type },
  tracked override val binoidal: Bifunctor.Into[category.type] {
    val source1: category.type
    val source2: category.type
  },
  structure: String = "Bifunctor",
)(using
  fixture: CategoryFixture.For[category.type],
  typename: TypeName[binoidal.Self],
  types: SampleTypes,
  sample: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[binoidal.F[X, Y]],
) extends BinoidalFunctorSpec(s"${typename.name} on ${fixture.name}", category, binoidal, structure) {
  import types.{T1, T2, T3, T4, given}
  import fixture.*
  import category.-->
  import binoidal.F
  import binoidal.BifunctorLaws.*

  private given BSample: [X: Sample, Y: Sample] => Sample[F[X, Y]] = sample[X, Y]

  also("Bifunctor") {
    law("identity") {
      val observations = observe[F[T1, T2], F[T1, T2]]

      forAll(observations) { observe =>
        given ((F[T1, T2] --> F[T1, T2]) is Observable) = observe
        identity[T1, T2]
      }
    }

    law("composition") {
      val observations = observe[F[T1, T2], F[T4, T3]]

      forAll(
        observations,
        Gen.zip(arrow[T1, T3], arrow[T2, T1]),
        Gen.zip(arrow[T3, T4], arrow[T1, T3]),
      ) { case (observe, (f1, g1), (f2, g2)) =>
        given ((F[T1, T2] --> F[T4, T3]) is Observable) = observe
        composition(f1, g1, f2, g2)
      }
    }

    law("congruence") {
      val observations = observe[F[T1, T2], F[T4, T3]]
      val fs           = arrow[T1, T4]
      val gs           = arrow[T2, T3]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((F[T1, T2] --> F[T4, T3]) is Observable) = observe
        congruence(f, variant(f), g, variant(g))
      }
    }
  }
}

class PartialTuple2IsBifunctorTest            extends BifunctorSpec(Partial, Partial.Tuple2IsBifunctor)
class PartialTuple2OpIsBifunctorTest          extends BifunctorSpec(Partial.op, Partial.Tuple2IsBifunctor.op)
class PartialTuple2BifunctorOpIsBifunctorTest extends BifunctorSpec(Partial.op, Bifunctor.Op(Partial.Tuple2IsBifunctor))
