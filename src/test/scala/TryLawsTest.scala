package parrot

import org.scalacheck.{Arbitrary, Gen}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

import scala.annotation.targetName
import scala.util.{Failure, Success, Try}

class TryLawsTest extends AnyFunSuite with ScalaCheckPropertyChecks {

  private val M  = Monad[Try]
  private val MP = MonoidPlus[Try]
  private val RM = RestrictionMonad[Try]
  private val EM = ElgotMonad[Try]

  import MP.+
  import RM.restrict

  // --- Observational Equivalence Helpers ---

  extension [A](t1: Try[A])
    @targetName("eqTry")
    infix def ===(t2: Try[A]): Boolean = (t1, t2) match {
      case (Success(a1), Success(a2)) => a1 == a2
      case (Failure(e1), Failure(e2)) => e1.getMessage == e2.getMessage
      case _                          => false
    }

  extension [A](t1: Try[A])
    // Equivalence up to failure identification
    @targetName("eqTryFailureNorm")
    infix def =~=(t2: Try[A]): Boolean = (t1, t2) match {
      case (Success(a1), Success(a2)) => a1 == a2
      case (Failure(_), Failure(_))   => true
      case _                          => false
    }

  given [A: Arbitrary] => Arbitrary[Try[A]] = Arbitrary(
    Gen.oneOf(
      Arbitrary.arbitrary[A].map(Success(_)),
      Arbitrary.arbitrary[String].map(msg => Failure(new Exception(msg))),
    )
  )

  // =========================================================================
  // 1. Functor Laws on Try
  // =========================================================================

  test("Functor: Try identity law") {
    forAll { (t: Try[Int]) =>
      assert(t.map(identity) === t)
    }
  }

  test("Functor: Try composition law") {
    forAll { (t: Try[Int]) =>
      val f: Int => String = _.toString
      val g: String => Int = _.length
      assert(t.map(f).map(g) === t.map(f.andThen(g)))
    }
  }

  // =========================================================================
  // 2. Monad Laws on Try
  // =========================================================================

  test("Monad: Try unit naturality law") {
    forAll { (a: Int) =>
      val f: Int => String = x => (x * 2).toString
      assert(M.unit(a).map(f) === M.unit(f(a)))
    }
  }

  test("Monad: Try left unitality law") {
    forAll { (t: Try[Int]) =>
      assert(M.unit(t).flatten === t)
    }
  }

  test("Monad: Try right unitality law") {
    forAll { (t: Try[Int]) =>
      assert(t.map(M.unit).flatten === t)
    }
  }

  test("Monad: Try flatten naturality law") {
    forAll { (t: Try[Try[Int]]) =>
      val f: Int => String = _.toString
      assert(t.flatten.map(f) === t.map(_.map(f)).flatten)
    }
  }

  test("Monad: Try associativity law") {
    forAll { (t: Try[Try[Try[Int]]]) =>
      assert(t.flatten.flatten === t.map(_.flatten).flatten)
    }
  }

  // =========================================================================
  // 3. MonoidPlus Laws on Try
  // =========================================================================

  test("MonoidPlus: Try left identity law") {
    forAll { (x: Try[Int]) =>
      assert(MP.zero[Int] + x === x)
    }
  }

  test("MonoidPlus: Try right identity law (up to failure equivalence)") {
    forAll { (x: Try[Int]) =>
      assert(x + MP.zero[Int] =~= x)
    }
  }

  test("MonoidPlus: Try associativity law") {
    forAll { (x: Try[Int], y: Try[Int], z: Try[Int]) =>
      assert((x + y) + z === x + (y + z))
    }
  }

  // =========================================================================
  // 4. RestrictionMonad Laws on Try
  // =========================================================================

  test("RestrictionMonad: Try idempotence law") {
    forAll { (t: Try[Int]) =>
      assert(t.restrict.restrict === t.restrict)
    }
  }

  test("RestrictionMonad: Try unitality law") {
    forAll { (a: Int) =>
      assert(RM.unit(a).restrict === RM.unit(()))
    }
  }

  test("RestrictionMonad: Try left absorption law") {
    forAll { (t: Try[Int]) =>
      assert(t.restrict.flatMap(_ => t) === t)
    }
  }

  test("RestrictionMonad: Try commutativity law (up to failure equivalence)") {
    forAll { (t1: Try[Int], t2: Try[String]) =>
      val lhs = t1.restrict.flatMap(_ => t2.restrict)
      val rhs = t2.restrict.flatMap(_ => t1.restrict)
      assert(lhs =~= rhs)
    }
  }

  // =========================================================================
  // 5. ElgotMonad Laws on Try
  // =========================================================================

  test("ElgotMonad: Try fixpoint law") {
    forAll { (n: Int) =>
      val f: Int => Try[Either[String, Int]] = x =>
        if x <= 0 then Success(Left(x.toString))
        else if x > 100 then Failure(Exception("too big"))
        else Success(Right(x - 1))

      val lhs = EM.iterate(f)(n)
      val rhs = f(n).flatMap {
        case Left(b)  => EM.unit(b)
        case Right(a) => EM.iterate(f)(a)
      }
      assert(lhs === rhs)
    }
  }

  test("ElgotMonad: Try naturality in parameters law") {
    forAll { (n: Int) =>
      val f: Int => Try[Either[Int, Int]] = x =>
        if x <= 0 then Success(Left(x))
        else if x > 100 then Failure(Exception("too big"))
        else Success(Right(x - 1))
      val g: Int => String = _.toString

      val lhs = EM.iterate(f)(n).map(g)
      val rhs = EM.iterate((a: Int) => f(a).map(_.left.map(g)))(n)
      assert(lhs === rhs)
    }
  }

  test("ElgotMonad: Try dinaturality law") {
    forAll { (n: Int) =>
      val f: Int => Try[Either[String, Int]] = x =>
        if x <= 0 then Success(Left(x.toString))
        else if x > 100 then Failure(Exception("too big"))
        else Success(Right(x))
      val g: Int => Int = c => c - 1

      val lhs = EM.iterate((a: Int) => f(a).map(_.map(g)))(n)
      val rhs = f(n).flatMap {
        case Left(b)  => EM.unit(b)
        case Right(c) => EM.iterate((c: Int) => f(g(c)))(c)
      }
      assert(lhs === rhs)
    }
  }

  test("ElgotMonad: Try codiagonal law") {
    forAll { (n: Int) =>
      val f: Int => Try[Either[Either[String, Int], Int]] = x =>
        if x <= 0 then Success(Left(Left(x.toString)))
        else if x > 100 then Failure(Exception("too big"))
        else if x % 2 == 0 then Success(Left(Right(x - 2)))
        else Success(Right(x - 1))

      val lhs = EM.iterate(EM.iterate(f))(n)
      val rhs = EM.iterate((a: Int) =>
        f(a).map {
          case Left(Left(b))  => Left(b)
          case Left(Right(a)) => Right(a)
          case Right(a)       => Right(a)
        }
      )(n)
      assert(lhs === rhs)
    }
  }

  test("ElgotMonad: Try uniformity law") {
    forAll { (n: Int) =>
      val h: Int => Int                      = _ + 1
      val g: Int => Try[Either[String, Int]] = y =>
        if y <= 0 then Success(Left(y.toString))
        else if y > 100 then Failure(Exception("too big"))
        else Success(Right(y - 2))

      val f: Int => Try[Either[String, Int]] = a =>
        g(h(a)).map(_.map(y => y - 1))

      val lhs = EM.iterate(f)(n)
      val rhs = EM.iterate(g)(h(n))
      assert(lhs === rhs)
    }
  }
}
