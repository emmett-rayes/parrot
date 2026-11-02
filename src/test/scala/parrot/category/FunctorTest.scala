package parrot
package category

import Category.Type

/** The laws of [[Functor]], for functors between categories whose objects are all types.
  *
  * Arrows come from the fixture of the source category, observations from the fixture of the target category.
  */
abstract class FunctorSpec(
  name: String,
  tracked val functor: Functor { val source: Category { type Obj = Type }; val target: Category { type Obj = Type } },
)(using
  source: CategoryFixture.On[functor.source.type],
  target: CategoryFixture.On[functor.target.type],
  types: SampleTypes,
  sample: [X] => Sample[X] ?-> Sample[functor.F[X]],
) extends LawSuite("Functor", name) {
  import types.{T1, T2, T4, given}
  import source.{arrow, variant}
  import target.observe
  import functor.F
  import functor.target.--> as ==>
  import functor.FunctorLaws.*

  private given FSample: [X: Sample] => Sample[F[X]] = sample[X]

  law("identity") {
    val observations = observe[F[T1], F[T1]]

    forAll(observations) { observe =>
      given ((F[T1] ==> F[T1]) is Observable) = observe
      identity[T1]
    }
  }

  law("composition") {
    val observations = observe[F[T1], F[T4]]
    val fs           = arrow[T1, T2]
    val gs           = arrow[T2, T4]

    forAll(observations, fs, gs) { (observe, f, g) =>
      given ((F[T1] ==> F[T4]) is Observable) = observe
      composition(f, g)
    }
  }

  law("congruence") {
    val observations = observe[F[T1], F[T2]]
    val fs           = arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given ((F[T1] ==> F[T2]) is Observable) = observe
      congruence(f, variant(f))
    }
  }
}

class IdentityIsFunctorTest  extends FunctorSpec("Identity", Total.Identity)
class OptionIsFunctorTest    extends FunctorSpec("Option", Monad.OptionIsMonad.functor)
class WriterIsFunctorTest    extends FunctorSpec("Writer[String]", StringWriter.functor)
class OptionTIsFunctorTest   extends FunctorSpec("OptionT[Writer[String]]", FailingStringWriter.functor)
class WriterTIsFunctorTest   extends FunctorSpec("WriterT[String, Option]", StringWriterOverOption.functor)
class StateIsFunctorTest     extends FunctorSpec("State[Boolean]", BooleanState.functor)
class StateTIsFunctorTest    extends FunctorSpec("State[Boolean, Option]", FailingBooleanState.functor)
class InclusionIsFunctorTest extends FunctorSpec("Inclusion of Total in Partial", Partial.Inclusion)
