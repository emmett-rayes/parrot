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

/** Computations that may fail and log strings, where a failure loses the log. */
object StringWriterOverOption extends WriterT(StringConcat, Monad.OptionIsMonad)

/** Computations that read and update a `Boolean` state: few enough states for computations to be data. */
object BooleanState extends State[Boolean]

/** Computations that read and update a `Boolean` state and may fail. */
object FailingBooleanState extends StateT[Boolean](Monad.OptionIsMonad)

class IdentityIsMonadTest extends MonadSpec("Identity", Monad.Identity)
class OptionIsMonadTest   extends MonadSpec("Option", Monad.OptionIsMonad)
class WriterIsMonadTest   extends MonadSpec("Writer[String]", StringWriter)
class OptionTIsMonadTest  extends MonadSpec("OptionT[Writer[String]]", FailingStringWriter)
class WriterTIsMonadTest  extends MonadSpec("WriterT[String, Option]", StringWriterOverOption)
class StateIsMonadTest    extends MonadSpec("State[Boolean]", BooleanState)
class StateTIsMonadTest   extends MonadSpec("State[Boolean, Option]", FailingBooleanState)

/** The order of failure and output: failure over a writer keeps the output of a computation that fails, and a writer
  * over failure loses it.
  */
class TransformerOrderTest extends org.scalatest.funsuite.AnyFunSuite {
  given CanEqual[Any, Any] = CanEqual.derived

  test("OptionT[Writer[String]]: a computation that fails keeps the output before it") {
    val failed = FailingStringWriter.bind[Unit, Int](_ => ("", None))(("a", Some(())))
    assert(failed == ("a", None))
  }

  test("WriterT[String, Option]: a computation that fails loses the output before it") {
    val failed = StringWriterOverOption.bind[Unit, Int](_ => None)(Some(("a", ())))
    assert(failed.isEmpty)
  }
}
