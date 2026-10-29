package parrot
package category

import Sample.given

/** The laws of [[Monad]], for monads on 𝒮. */
abstract class MonadSpec(name: String, tracked val M: Monad.On[Total.type])(using
  types: SampleTypes,
  sample: [X] => Sample[X] ?-> Sample[M.M[X]],
) extends LawSuite("Monad", name) {
  import types.{T1, T2, given}
  import M.M
  import M.MonadLaws.*

  private given MSample: [X: Sample] => Sample[M[X]] = sample[X]

  law("leftUnit") {
    val observations = TotalFixture.observe[M[T1], M[T1]]

    forAll(observations) { observe =>
      given ((M[T1] -> M[T1]) is Observable) = observe
      leftUnit[T1]
    }
  }

  law("rightUnit") {
    val observations = TotalFixture.observe[M[T1], M[T1]]

    forAll(observations) { observe =>
      given ((M[T1] -> M[T1]) is Observable) = observe
      rightUnit[T1]
    }
  }

  law("associativity") {
    val observations = TotalFixture.observe[M[M[M[T1]]], M[T1]]

    forAll(observations) { observe =>
      given ((M[M[M[T1]]] -> M[T1]) is Observable) = observe
      associativity[T1]
    }
  }

  law("unitNaturality") {
    val observations = TotalFixture.observe[T1, M[T2]]
    val fs           = TotalFixture.arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given ((T1 -> M[T2]) is Observable) = observe
      unitNaturality(f)
    }
  }

  law("flattenNaturality") {
    val observations = TotalFixture.observe[M[M[T1]], M[T2]]
    val fs           = TotalFixture.arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given ((M[M[T1]] -> M[T2]) is Observable) = observe
      flattenNaturality(f)
    }
  }
}

/** The writer monad of string concatenation: a log of what happened, in order. */
object StringWriter extends Writer(StringConcat)

/** Computations that log strings and may fail: the effects of the reference parser without its state. */
object FailingStringWriter extends OptionT(StringWriter)

/** Computations that read and update a `Boolean` state and may fail: few enough states for computations to be data. */
object BooleanState extends StateT[Boolean](Monad.OptionIsMonad)

class OptionIsMonadTest  extends MonadSpec("Option", Monad.OptionIsMonad)
class WriterIsMonadTest  extends MonadSpec("Writer[String]", StringWriter)
class OptionTIsMonadTest extends MonadSpec("OptionT[Writer[String]]", FailingStringWriter)
class StateIsMonadTest   extends MonadSpec("State[Boolean, Option]", BooleanState)
