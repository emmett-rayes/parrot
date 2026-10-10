package parrot
package category

class MonadTest extends CategorySuite {

  private val OptionMonad = Monad.OptionIsMonad
  import OptionMonad.{plus, restrict}

  private val f: Int => Option[String]    = i => if i % 3 == 0 then None else Some(s"v$i")
  private val g: String => Option[Boolean] = s => if s.length > 3 then Some(true) else None

  test("Option is Monad: monad laws") {
    forAll { (i: Int, m: Option[Int]) =>
      val _ = assert(OptionMonad.MonadLaws.leftIdentity(i, f))
      val _ = assert(OptionMonad.MonadLaws.rightIdentity(m))
      assert(OptionMonad.MonadLaws.associativity(m, f, g))
    }
  }

  test("Option is Monad.Plus: plus laws") {
    forAll { (m: Option[Int], n: Option[Int], o: Option[Int]) =>
      val _ = assert(OptionMonad.PlusLaws.leftIdentity(m))
      val _ = assert(OptionMonad.PlusLaws.rightIdentity(m))
      val _ = assert(OptionMonad.PlusLaws.associativity(m, n, o))
      assert(OptionMonad.PlusLaws.leftZero(f))
    }
  }

  test("Option is Monad.Restriction: restriction laws") {
    forAll { (i: Int, m: Option[Int], n: Option[String]) =>
      val _ = assert(OptionMonad.RestrictionLaws.absorption(m))
      val _ = assert(OptionMonad.RestrictionLaws.commutativity(m, n))
      assert(OptionMonad.RestrictionLaws.unitality(i))
    }
  }

  test("Option is Monad.Elgot: iteration computes a tail-recursive loop") {
    val countdown: Int => Option[Either[String, Int]] = i => {
      if i < 0 then None else if i == 0 then Some(Left("done")) else Some(Right(i - 1))
    }
    val _ = assert(OptionMonad.iterate(countdown)(100000) == Some("done"))
    val _ = assert(OptionMonad.iterate(countdown)(-1) == None)
    forAll((i: Int) => assert(OptionMonad.ElgotLaws.fixedPoint(countdown, i % 100)))
  }

  test("Option is Monad: extensions behave as Option") {
    val _ = assert(OptionMonad.flatMap(Some(1))(i => Some(i + 1)) == Some(2))
    val _ = assert((None: Option[Int]).plus(Some(1)) == Some(1))
    assert(Some(1).restrict == Some(()))
  }
}
