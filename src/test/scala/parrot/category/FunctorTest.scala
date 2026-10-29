package parrot
package category

/** The laws of [[Functor]], for functors between categories whose objects are all types.
  *
  * Arrows come from the fixture of the source category, observations from the fixture of the target category.
  */
abstract class FunctorSpec(
  name: String,
  tracked val F: Functor { val C: Category { type Obj = Type }; val D: Category { type Obj = Type } },
)(using
  source: CategoryFixture.On[F.C.type],
  target: CategoryFixture.On[F.D.type],
  types: SampleTypes,
  sample: [X] => Sample[X] ?-> Sample[F.F[X]],
) extends LawSuite("Functor", name) {
  import types.{T1, T2, T4, given}
  import source.{arrow, variant}
  import target.observe
  import F.F
  import F.D.--> as ->>
  import F.FunctorLaws.*

  private given FSample: [X: Sample] => Sample[F[X]] = sample[X]

  law("identity") {
    val observations = observe[F[T1], F[T1]]

    forAll(observations) { observe =>
      given ((F[T1] ->> F[T1]) is Observable) = observe
      identity[T1]
    }
  }

  law("composition") {
    val observations = observe[F[T1], F[T4]]
    val fs           = arrow[T1, T2]
    val gs           = arrow[T2, T4]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given ((F[T1] ->> F[T4]) is Observable) = observe
      composition(f, g)
    }
  }

  law("congruence") {
    val observations = observe[F[T1], F[T2]]
    val fs           = arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given ((F[T1] ->> F[T2]) is Observable) = observe
      congruence(f, variant(f))
    }
  }
}

class OptionIsFunctorTest    extends FunctorSpec("Option", Endofunctor.OptionIsEndofunctor)
class WriterIsFunctorTest    extends FunctorSpec("Writer[String]", StringWriter.F)
class OptionTIsFunctorTest   extends FunctorSpec("OptionT[Writer[String]]", FailingStringWriter.F)
class StateIsFunctorTest     extends FunctorSpec("State[Boolean, Option]", BooleanState.F)
class InclusionIsFunctorTest extends FunctorSpec("Inclusion of Total in Partial", Partial.Inclusion)
