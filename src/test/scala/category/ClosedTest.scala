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
}
