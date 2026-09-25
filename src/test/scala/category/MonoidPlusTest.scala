package parrot
package category

import org.scalacheck.{Arbitrary, Gen, Prop, Test}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

import scala.util.{Failure, Success, Try}

class MonoidPlusTest extends AnyFunSuite with ScalaCheckPropertyChecks {

  // =========================================================================
  // Monoid+ Laws on Option[Int]
  // =========================================================================

  private val optionMonoid = summon[Option[Int] is `Monoid+`]
  private val OptionLaws   = optionMonoid.`Monoid+Laws`

  given OptionIsEq: [A: Eq] => Option[A] is Eq {
    def eq(a: Option[A], b: Option[A]): Boolean = {
      (a, b) match {
        case (Some(x), Some(y)) => x === y
        case (None, None)       => true
        case _                  => false
      }
    }
  }

  test("Option is Monoid+: left identity law") {
    forAll { (x: Option[Int]) =>
      assert(OptionLaws.leftIdentity(x))
    }
  }

  test("Option is Monoid+: right identity law") {
    forAll { (x: Option[Int]) =>
      assert(OptionLaws.rightIdentity(x))
    }
  }

  test("Option is Monoid+: associativity law") {
    forAll { (x: Option[Int], y: Option[Int], z: Option[Int]) =>
      assert(OptionLaws.associativity(x, y, z))
    }
  }

  // =========================================================================
  // Monoid+ Laws on Try[Int]
  // =========================================================================

  private val tryMonoid = summon[Try[Int] is `Monoid+`]
  private val TryLaws   = tryMonoid.`Monoid+Laws`

  given ArbitraryTry: [A: Arbitrary] => Arbitrary[Try[A]] = Arbitrary {
    Gen.oneOf(
      Arbitrary.arbitrary[A].map(Success(_)),
      Gen.const(Failure(new RuntimeException("test error")))
    )
  }

  given TryIsEq: [A: Eq] => Try[A] is Eq {
    def eq(a: Try[A], b: Try[A]): Boolean = {
      (a, b) match {
        case (Success(x), Success(y)) => x === y
        case (Failure(_), Failure(_)) => true
        case _                        => false
      }
    }
  }

  test("Try is Monoid+: left identity law") {
    forAll { (x: Try[Int]) =>
      assert(TryLaws.leftIdentity(x))
    }
  }

  test("Try is Monoid+: right identity law") {
    forAll { (x: Try[Int]) =>
      assert(TryLaws.rightIdentity(x))
    }
  }

  test("Try is Monoid+: associativity law") {
    forAll { (x: Try[Int], y: Try[Int], z: Try[Int]) =>
      assert(TryLaws.associativity(x, y, z))
    }
  }

  // =========================================================================
  // Monoid+ Laws on Function (Int => Option[String])
  // =========================================================================

  private val functionMonoid = summon[(Int => Option[String]) is `Monoid+`]
  private val FunctionLaws   = functionMonoid.`Monoid+Laws`

  given ArbitraryFunctionIsEq: [A: Arbitrary, B: Eq] => (A => B) is Eq {
    def eq(f: A => B, g: A => B): Boolean = {
      val prop = Prop.forAll((a: A) => f(a) === g(a))
      Test.check(Test.Parameters.default, prop).passed
    }
  }

  given ArbitraryOption: [A: Arbitrary] => Arbitrary[Option[A]] = Arbitrary {
    Gen.oneOf(
      Arbitrary.arbitrary[A].map(Some(_)),
      Gen.const(None)
    )
  }

  test("Function is Monoid+: left identity law") {
    forAll { (x: Int => Option[String]) =>
      assert(FunctionLaws.leftIdentity(x))
    }
  }

  test("Function is Monoid+: right identity law") {
    forAll { (x: Int => Option[String]) =>
      assert(FunctionLaws.rightIdentity(x))
    }
  }

  test("Function is Monoid+: associativity law") {
    forAll { (x: Int => Option[String], y: Int => Option[String], z: Int => Option[String]) =>
      assert(FunctionLaws.associativity(x, y, z))
    }
  }
}
