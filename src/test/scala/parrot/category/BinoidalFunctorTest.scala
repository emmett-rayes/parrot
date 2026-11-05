package parrot
package category

import Category.Type

/** The laws of [[BinoidalFunctor]], for binoidal functors **C** × **C** → **C** on a category whose objects are all
  * types.
  */
abstract class BinoidalFunctorSpec(
  name: String,
  tracked val category: Category { type Obj = Type },
  tracked val binoidal: BinoidalFunctor.Into[category.type] { val source1: category.type; val source2: category.type },
  structure: String = "BinoidalFunctor",
)(using
  fixture: CategoryFixture.For[category.type],
  types: SampleTypes,
  sample: [X, Y] => (Sample[X], Sample[Y]) ?-> Sample[binoidal.F[X, Y]],
) extends LawSuite(structure, name) {
  import types.{T1, T2, T3, T4, given}
  import fixture.*
  import category.-->
  import binoidal.F
  import binoidal.BinoidalFunctorLaws.*

  private given BSample: [X: Sample, Y: Sample] => Sample[F[X, Y]] = sample[X, Y]

  also("BinoidalFunctor") {
    law("lmapIdentity") {
      val observations = observe[F[T1, T2], F[T1, T2]]

      forAll(observations) { observe =>
        given ((F[T1, T2] --> F[T1, T2]) is Observable) = observe
        lmapIdentity[T1, T2]
      }
    }

    law("lmapComposition") {
      val observations = observe[F[T1, T2], F[T4, T2]]
      val f1s          = arrow[T1, T3]
      val f2s          = arrow[T3, T4]

      forAll(observations, f1s, f2s) { (observe, f1, f2) =>
        given ((F[T1, T2] --> F[T4, T2]) is Observable) = observe
        lmapComposition[T1, T3, T4, T2](f1, f2)
      }
    }

    law("lmapCongruence") {
      val observations = observe[F[T1, T2], F[T3, T2]]
      val fs           = arrow[T1, T3]

      forAll(observations, fs) { (observe, f) =>
        given ((F[T1, T2] --> F[T3, T2]) is Observable) = observe
        lmapCongruence[T1, T3, T2](f, variant(f))
      }
    }

    law("rmapIdentity") {
      val observations = observe[F[T2, T1], F[T2, T1]]

      forAll(observations) { observe =>
        given ((F[T2, T1] --> F[T2, T1]) is Observable) = observe
        rmapIdentity[T1, T2]
      }
    }

    law("rmapComposition") {
      val observations = observe[F[T2, T1], F[T2, T4]]
      val g1s          = arrow[T1, T3]
      val g2s          = arrow[T3, T4]

      forAll(observations, g1s, g2s) { (observe, g1, g2) =>
        given ((F[T2, T1] --> F[T2, T4]) is Observable) = observe
        rmapComposition[T1, T3, T4, T2](g1, g2)
      }
    }

    law("rmapCongruence") {
      val observations = observe[F[T2, T1], F[T2, T3]]
      val gs           = arrow[T1, T3]

      forAll(observations, gs) { (observe, g) =>
        given ((F[T2, T1] --> F[T2, T3]) is Observable) = observe
        rmapCongruence[T1, T3, T2](g, variant(g))
      }
    }
  }
}

class OptionKleisliProductIsBinoidalFunctorTest
    extends BinoidalFunctorSpec(
      "Kleisli[Option] on Product",
      Kleisli.OptionKleisli.arrows,
      Freyd.Tensor(Kleisli.OptionProduct),
    )

class OptionKleisliCoproductIsBinoidalFunctorTest
    extends BinoidalFunctorSpec(
      "Kleisli[Option] on Coproduct",
      Kleisli.OptionKleisli.arrows,
      Freyd.Tensor(Kleisli.OptionCoproduct),
    )

class StringWriterKleisliProductIsBinoidalFunctorTest
    extends BinoidalFunctorSpec(
      "Kleisli[Writer[String]] on Product",
      StringWriterKleisli.arrows,
      Freyd.Tensor(StringWriterProduct),
    )

class StringWriterKleisliCoproductIsBinoidalFunctorTest
    extends BinoidalFunctorSpec(
      "Kleisli[Writer[String]] on Coproduct",
      StringWriterKleisli.arrows,
      Freyd.Tensor(StringWriterCoproduct),
    )
