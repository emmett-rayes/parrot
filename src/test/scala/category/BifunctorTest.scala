package parrot
package category

import org.scalacheck.Gen

/** The laws of [[Bifunctor]], for bifunctors **K** × **K** → **K** on a category whose objects are all types. */
abstract class BifunctorSpec(
  tracked val F: Fixture,
  tracked val B: Bifunctor { val C1: F.K.type; val C2: F.K.type; val D: F.K.type },
)(using
  bifunctor: TypeName[B.Self],
  category: TypeName[F.K.type],
  types: SampleTypes,
  sample: [X, Y] => (Sample[X], Sample[Y]) ?=> Sample[B.F[X, Y]],
) extends LawSuite("Bifunctor", s"${bifunctor.name} on ${category.name}") {
  import types.{T1, T2, T3, T4, given}
  import F.K.-->
  import B.BifunctorLaws.*

  private given BSample: [X: Sample, Y: Sample] => Sample[B.F[X, Y]] = sample[X, Y]

  law("identity") {
    val observations = F.observe[B.F[T1, T2], B.F[T1, T2]]
    forAll(observations) { observe =>
      given ((B.F[T1, T2] --> B.F[T1, T2]) is Observable) = observe
      identity[T1, T2]
    }
  }

  law("composition") {
    val observations = F.observe[B.F[T1, T2], B.F[T4, T3]]
    forAll(
      observations,
      Gen.zip(F.arrow[T1, T3], F.arrow[T2, T1]),
      Gen.zip(F.arrow[T3, T4], F.arrow[T1, T3]),
    ) { case (observe, (f1, g1), (f2, g2)) =>
      given ((B.F[T1, T2] --> B.F[T4, T3]) is Observable) = observe
      composition(f1, g1, f2, g2)
    }
  }

  law("congruence") {
    val observations = F.observe[B.F[T1, T2], B.F[T4, T3]]
    val fs           = F.arrow[T1, T4]
    val gs           = F.arrow[T2, T3]
    forAll(observations, fs, gs) { (observe, f, g) =>
      given ((B.F[T1, T2] --> B.F[T4, T3]) is Observable) = observe
      congruence(f, F.variant(f), g, F.variant(g))
    }
  }
}

class ScalaTuple2IsBifunctorTest   extends BifunctorSpec(TotalFixture, Total.Tuple2IsBifunctor)
class ScalaEitherIsBifunctorTest   extends BifunctorSpec(TotalFixture, Total.EitherIsBifunctor)
class PartialTuple2IsBifunctorTest extends BifunctorSpec(PartialFixture, Partial.Tuple2IsBifunctor)
class PartialEitherIsBifunctorTest extends BifunctorSpec(PartialFixture, Partial.EitherIsBifunctor)
