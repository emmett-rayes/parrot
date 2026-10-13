package parrot
package category

import scala.util.{Failure, Success, Try}

class MonadTest extends CategorySuite {

  private val OptionMonad       = Monad.OptionIsMonad
  private val OptionRestriction = RestrictionMonad.OptionIsRestrictionMonad
  private val OptionElgot       = ElgotMonad.OptionIsElgotMonad
  private val TryMonad          = Monad.TryIsMonad

  import OptionRestriction.restrict

  private val f: Int => Option[String]    = i => if i % 3 == 0 then None else Some(s"v$i")
  private val g: String => Option[Boolean] = s => if s.length > 3 then Some(true) else None

  private val fTry: Int => Try[String]    = i => if i % 3 == 0 then Failure(new Exception("div3")) else Success(s"v$i")
  private val gTry: String => Try[Boolean] = s => if s.length > 3 then Success(true) else Failure(new Exception("short"))

  test("Option is Monad: monad laws") {
    forAll { (i: Int, m: Option[Int]) =>
      val _ = assert(OptionMonad.MonadLaws.leftIdentity(i, f))
      val _ = assert(OptionMonad.MonadLaws.rightIdentity(m))
      assert(OptionMonad.MonadLaws.associativity(m, f, g))
    }
  }

  test("Option is Monad: unit and multiplication laws") {
    forAll { (i: Int, m: Option[Int], mm: Option[Option[Int]], mmm: Option[Option[Option[Int]]]) =>
      val h: Int => String = _.toString
      val _ = assert(OptionMonad.MonadLaws.unitNaturality(i, h))
      val _ = assert(OptionMonad.MonadLaws.leftUnitality(m))
      val _ = assert(OptionMonad.MonadLaws.rightUnitality(m))
      val _ = assert(OptionMonad.MonadLaws.multiplicationNaturality(mm, h))
      assert(OptionMonad.MonadLaws.multiplicationAssociativity(mmm))
    }
  }

  test("Option is Restriction: restriction laws") {
    forAll { (i: Int, m: Option[Int], n: Option[String]) =>
      val _ = assert(OptionRestriction.RestrictionLaws.absorption(m))
      val _ = assert(OptionRestriction.RestrictionLaws.commutativity(m, n))
      val _ = assert(OptionRestriction.RestrictionLaws.unitality(i))
      assert(OptionRestriction.RestrictionLaws.idempotence(m))
    }
  }

  test("Option is Elgot: iteration computes a tail-recursive loop") {
    val countdown: Int => Option[Either[String, Int]] = i => {
      if i < 0 then None else if i == 0 then Some(Left("done")) else Some(Right(i - 1))
    }
    val _ = assert(OptionElgot.iterate(countdown)(100000) == Some("done"))
    val _ = assert(OptionElgot.iterate(countdown)(-1) == None)
    forAll((i: Int) => assert(OptionElgot.ElgotLaws.fixedPoint(countdown, i % 100)))
  }

  test("Option is Monad: extensions behave as Option") {
    val _ = assert(OptionMonad.flatMap(Some(1))(i => Some(i + 1)) == Some(2))
    val _ = assert(OptionMonad.flatten(Some(Some(1))) == Some(1))
    val _ = assert(OptionMonad.flatten(Some(None: Option[Int])) == None)
    val _ = assert(OptionMonad.flatten(None: Option[Option[Int]]) == None)
    val _ = assert(OptionMonad.SelfIsFunctor.map(Some(1))(_ + 1) == Some(2))
    val _ = assert(Some(Some(1)).flatten == Some(1))
    assert(Some(1).restrict == Some(()))
  }

  test("Try is Monad: monad laws") {
    forAll { (i: Int, m: Try[Int]) =>
      val _ = assert(TryMonad.MonadLaws.leftIdentity(i, fTry))
      val _ = assert(TryMonad.MonadLaws.rightIdentity(m))
      assert(TryMonad.MonadLaws.associativity(m, fTry, gTry))
    }
  }

  test("Try is Monad: unit and multiplication laws") {
    forAll { (i: Int, m: Try[Int], mm: Try[Try[Int]], mmm: Try[Try[Try[Int]]]) =>
      val h: Int => String = _.toString
      val _ = assert(TryMonad.MonadLaws.unitNaturality(i, h))
      val _ = assert(TryMonad.MonadLaws.leftUnitality(m))
      val _ = assert(TryMonad.MonadLaws.rightUnitality(m))
      val _ = assert(TryMonad.MonadLaws.multiplicationNaturality(mm, h))
      assert(TryMonad.MonadLaws.multiplicationAssociativity(mmm))
    }
  }

  test("Try is Monad: extensions behave as Try") {
    val _ = assert(TryMonad.flatMap(Success(1))(i => Success(i + 1)) === Success(2))
    val _ = assert(TryMonad.flatten(Success(Success(1))) === Success(1))
    val ex = new Exception("boom")
    val _ = assert(TryMonad.flatten(Success(Failure(ex)): Try[Try[Int]]) === Failure(ex))
    val _ = assert(TryMonad.flatten(Failure(ex): Try[Try[Int]]) === Failure(ex))
    assert(TryMonad.SelfIsFunctor.map(Success(1))(_ + 1) === Success(2))
  }
}
