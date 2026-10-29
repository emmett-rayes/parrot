package parrot
package category

import org.scalacheck.Gen

import Sample.given

/** The laws of [[Closed]] for the function types of 𝒮. */
class ScalaExponentialIsClosedTest extends LawSuite("Closed", "Exponential on Total") {
  import Total.Exponential.ClosedLaws.*

  /** Observes curried functions at pairs of sample points. */
  private val curried: Gen[(Int -> String -> Long) is Observable] = {
    for {
      ints    <- Sample.points[Int]
      strings <- Sample.points[String]
    } yield Observable.through[Int -> String -> Long, Long](
      for { i <- ints; s <- strings } yield (g: Int -> String -> Long) => g(i)(s)
    )
  }

  /** Observes maps between function types at sample functions. */
  private def onFunctions[X1: Sample, Y1: Sample, X2: Sample, Y2: Sample]
    : Gen[((X1 -> Y1) -> (X2 -> Y2)) is Observable] = {
    for {
      functions <- Gen.listOfN(4, TotalFixture.arrow[X1, Y1])
      observe   <- TotalFixture.observe[X2, Y2]
    } yield Observable.through[(X1 -> Y1) -> (X2 -> Y2), X2 -> Y2](functions.map(h => k => k(h)))(using observe)
  }

  law("beta") {
    val observations = TotalFixture.observe[(Int, String), Long]
    val fs           = TotalFixture.arrow[(Int, String), Long]

    forAll(observations, fs) { (observe, f) =>
      given ((((Int, String)) -> Long) is Observable) = observe
      beta(f)
    }
  }

  law("eta") {
    forAll(curried, Gen.function1[Int, String -> Long](Sample.function[String, Long])(using Sample.IntSample.cogen)) {
      (observe, g) =>
        given ((Int -> String -> Long) is Observable) = observe
        eta(g)
    }
  }

  law("curryCongruence") {
    val fs = TotalFixture.arrow[(Int, String), Long]

    forAll(curried, fs) { (observe, f) =>
      given ((Int -> String -> Long) is Observable) = observe
      curryCongruence(f, TotalFixture.variant[(Int, String), Long](f))
    }
  }

  also("Profunctor") {
    import Total.Exponential.internalHom.BifunctorLaws.*

    law("identity") {
      forAll(onFunctions[Int, String, Int, String]) { observe =>
        given (((Int -> String) -> (Int -> String)) is Observable) = observe
        identity[Int, String]
      }
    }

    law("composition") {
      forAll(
        onFunctions[Int, String, Long, Boolean],
        Gen.zip(TotalFixture.arrow[Boolean, Int], TotalFixture.arrow[String, Int]),
        Gen.zip(TotalFixture.arrow[Long, Boolean], TotalFixture.arrow[Int, Boolean]),
      ) { case (observe, (f1, g1), (f2, g2)) =>
        given (((Int -> String) -> (Long -> Boolean)) is Observable) = observe
        composition[Int, String, Boolean, Int, Long, Boolean](f1, g1, f2, g2)
      }
    }

    law("congruence") {
      val fs = TotalFixture.arrow[Long, Int]
      val gs = TotalFixture.arrow[String, Boolean]

      forAll(onFunctions[Int, String, Long, Boolean], fs, gs) { (observe, f, g) =>
        given (((Int -> String) -> (Long -> Boolean)) is Observable) = observe
        congruence[Int, String, Long, Boolean](f, TotalFixture.variant(f), g, TotalFixture.variant(g))
      }
    }
  }
}
