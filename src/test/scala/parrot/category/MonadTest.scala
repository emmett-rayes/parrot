package parrot
package category

import Sample.given

/** The laws of [[Monad]] and of its endofunctor, for monads on 𝒮. */
abstract class MonadSpec(name: String, tracked val M: Monad.On[Total.type])(using
  types: SampleTypes,
  sample: [X] => Sample[X] ?-> Sample[M.M[X]],
) extends LawSuite("Monad", name) {
  import types.{T1, T2, T4, given}
  import M.MonadLaws.*

  private given MSample: [X: Sample] => Sample[M.M[X]] = sample[X]

  law("leftUnit") {
    val observations = TotalFixture.observe[M.M[T1], M.M[T1]]

    forAll(observations) { observe =>
      given ((M.M[T1] -> M.M[T1]) is Observable) = observe
      leftUnit[T1]
    }
  }

  law("rightUnit") {
    val observations = TotalFixture.observe[M.M[T1], M.M[T1]]

    forAll(observations) { observe =>
      given ((M.M[T1] -> M.M[T1]) is Observable) = observe
      rightUnit[T1]
    }
  }

  law("associativity") {
    val observations = TotalFixture.observe[M.M[M.M[M.M[T1]]], M.M[T1]]

    forAll(observations) { observe =>
      given ((M.M[M.M[M.M[T1]]] -> M.M[T1]) is Observable) = observe
      associativity[T1]
    }
  }

  law("unitNaturality") {
    val observations = TotalFixture.observe[T1, M.M[T2]]
    val fs           = TotalFixture.arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given ((T1 -> M.M[T2]) is Observable) = observe
      unitNaturality(f)
    }
  }

  law("flattenNaturality") {
    val observations = TotalFixture.observe[M.M[M.M[T1]], M.M[T2]]
    val fs           = TotalFixture.arrow[T1, T2]

    forAll(observations, fs) { (observe, f) =>
      given ((M.M[M.M[T1]] -> M.M[T2]) is Observable) = observe
      flattenNaturality(f)
    }
  }

  also("Functor") {
    import M.F.FunctorLaws.*

    law("identity") {
      val observations = TotalFixture.observe[M.M[T1], M.M[T1]]

      forAll(observations) { observe =>
        given ((M.M[T1] -> M.M[T1]) is Observable) = observe
        identity[T1]
      }
    }

    law("composition") {
      val observations = TotalFixture.observe[M.M[T1], M.M[T4]]
      val fs           = TotalFixture.arrow[T1, T2]
      val gs           = TotalFixture.arrow[T2, T4]

      forAll(observations, fs, gs) { (observe, f, g) =>
        given ((M.M[T1] -> M.M[T4]) is Observable) = observe
        composition(f, g)
      }
    }

    law("congruence") {
      val observations = TotalFixture.observe[M.M[T1], M.M[T2]]
      val fs           = TotalFixture.arrow[T1, T2]

      forAll(observations, fs) { (observe, f) =>
        given ((M.M[T1] -> M.M[T2]) is Observable) = observe
        congruence(f, TotalFixture.variant(f))
      }
    }
  }
}

/** The writer monad of string concatenation: a log of what happened, in order. */
object StringWriter extends Writer(StringConcat)

class OptionIsMonadTest extends MonadSpec("Option", Monad.OptionIsMonad)
class WriterIsMonadTest extends MonadSpec("Writer[String]", StringWriter)
