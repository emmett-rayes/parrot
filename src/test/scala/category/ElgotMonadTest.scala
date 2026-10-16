package parrot
package category

import scala.util.{Failure, Success, Try}

class ElgotMonadTest extends CategorySuite {

  private val OptionElgot = ElgotMonad.OptionIsElgotMonad
  private val TryElgot    = ElgotMonad.TryIsElgotMonad

  test("Option is ElgotMonad: iteration computes a tail-recursive loop") {
    val countdown: Int => Option[Either[String, Int]] = i => {
      if i < 0 then None else if i == 0 then Some(Left("done")) else Some(Right(i - 1))
    }
    val _ = assert(OptionElgot.iterate(countdown)(100000) == Some("done"))
    val _ = assert(OptionElgot.iterate(countdown)(-1) == None)
    forAll((i: Int) => assert(OptionElgot.ElgotLaws.fixedPoint(countdown, i % 100)))
  }

  test("Try is ElgotMonad: iteration computes a tail-recursive loop") {
    val err =
      new IllegalArgumentException("negative")
    val countdown: Int => Try[Either[String, Int]] = i => {
      if i < 0 then Failure(err)
      else if i == 0 then Success(Left("done"))
      else Success(Right(i - 1))
    }
    val _ = assert(TryElgot.iterate(countdown)(100000) === (Success("done"): Try[String]))
    val _ = assert(TryElgot.iterate(countdown)(-1) === (Failure(err): Try[String]))
    forAll((i: Int) => assert(TryElgot.ElgotLaws.fixedPoint(countdown, i % 100)))
  }

  test("Try is ElgotMonad: fixed point law") {
    forAll { (n: Int) =>
      val f: Int => Try[Either[String, Int]] = x =>
        if x <= 0 then Success(Left(x.toString))
        else if x > 100 then Failure(new Exception("too big"))
        else Success(Right(x - 1))

      assert(TryElgot.ElgotLaws.fixedPoint(f, n % 100))
    }
  }
}
