package parrot
package category

import scala.util.Try

class RestrictionMonadTest extends CategorySuite {

  private val OptionRestriction = RestrictionMonad.OptionIsRestrictionMonad
  private val TryRestriction    = RestrictionMonad.TryIsRestrictionMonad

  import OptionRestriction.restrict

  test("Option is RestrictionMonad: restriction laws") {
    forAll { (i: Int, m: Option[Int], n: Option[String]) =>
      val _ = assert(OptionRestriction.RestrictionLaws.absorption(m))
      val _ = assert(OptionRestriction.RestrictionLaws.commutativity(m, n))
      val _ = assert(OptionRestriction.RestrictionLaws.unitality(i))
      assert(OptionRestriction.RestrictionLaws.idempotence(m))
    }
  }

  test("Option is RestrictionMonad: restrict behaves as Option.map(_ => ())") {
    val _ = assert(Some(42).restrict == Some(()))
    assert((None: Option[Int]).restrict == None)
  }

  test("Try is RestrictionMonad: restriction laws") {
    forAll { (i: Int, m: Try[Int], n: Try[String]) =>
      val _ = assert(TryRestriction.RestrictionLaws.absorption(m))
      val _ = assert(TryRestriction.RestrictionLaws.commutativity(m, n))
      val _ = assert(TryRestriction.RestrictionLaws.unitality(i))
      assert(TryRestriction.RestrictionLaws.idempotence(m))
    }
  }

  test("Try is RestrictionMonad: restrict behaves as Try.map(_ => ())") {
    import TryRestriction.restrict
    import scala.util.{Failure, Success}
    val _ = assert(Success(42).restrict === Success(()))
    val ex = new Exception("boom")
    assert(Failure(ex).restrict === Failure(ex))
  }
}
