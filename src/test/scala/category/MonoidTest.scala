package parrot
package category

import org.scalacheck.{Arbitrary, Gen, Prop, Test}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

import scala.util.{Failure, Success, Try}

class MonoidTest extends AnyFunSuite with ScalaCheckPropertyChecks {

  // =========================================================================
  // Arbitrary instances and Function Eq for law testing
  // =========================================================================

  given ArbitraryTry: [A: Arbitrary] => Arbitrary[Try[A]] = Arbitrary {
    Gen.oneOf(
      Arbitrary.arbitrary[A].map(Success(_)),
      Gen.const(Failure(new RuntimeException("test error")))
    )
  }

  given ArbitraryOption: [A: Arbitrary] => Arbitrary[Option[A]] = Arbitrary {
    Gen.oneOf(
      Arbitrary.arbitrary[A].map(Some(_)),
      Gen.const(None)
    )
  }

  given ArbitraryFunctionIsEq: [A: Arbitrary, B: Eq] => Function[A, B] is Eq {
    def eq(f: A => B, g: A => B): Boolean = {
      val prop = Prop.forAll((a: A) => f(a) === g(a))
      Test.check(Test.Parameters.default, prop).passed
    }
  }

  // =========================================================================
  // Option[Int] Additive & Monoid Object
  // =========================================================================

  private val optionAdditive = Monoid.Additive[Option[Int]]

  test("Option[Int] has Monoid.Additive instance") {
    import optionAdditive.+
    val one: Option[Int]  = Some(1)
    val two: Option[Int]  = Some(2)
    val none: Option[Int] = None
    val _                 = assert(optionAdditive.zero === None)
    val _                 = assert(optionAdditive.plus(one, two) === Some(1))
    val _                 = assert((one + two) === Some(1))
    val _                 = assert((none + two) === Some(2))
  }

  test("Option[Int] conforms to internal Monoid object") {
    val mObj = optionAdditive
    val _    = assert((mObj.unit(()): Option[Int]) === None)
    val _    = assert((mObj.multiply((Some(1), Some(2))): Option[Int]) === Some(1))
    val _    = assert((mObj.multiply((None, Some(2))): Option[Int]) === Some(2))
  }

  test("Option[Int] satisfies Monoid left identity law") {
    val _ = assert(optionAdditive.MonoidLaws.leftIdentity)
  }

  test("Option[Int] satisfies Monoid right identity law") {
    val _ = assert(optionAdditive.MonoidLaws.rightIdentity)
  }

  test("Option[Int] satisfies Monoid associativity law") {
    val _ = assert(optionAdditive.MonoidLaws.associativity)
  }

  // =========================================================================
  // Try[Int] Additive & Monoid Object
  // =========================================================================

  private val tryAdditive = Monoid.Additive[Try[Int]]

  test("Try[Int] has Monoid.Additive instance") {
    import tryAdditive.+
    val s1: Try[Int]   = Success(1)
    val s2: Try[Int]   = Success(2)
    val fErr: Try[Int] = Failure(new Exception())
    val _              = assert(tryAdditive.zero.isFailure)
    val _              = assert((s1 + s2) === Success(1))
    val _              = assert((fErr + s2) === Success(2))
  }

  test("Try[Int] conforms to internal Monoid object") {
    val mObj         = tryAdditive
    val s1: Try[Int] = Success(1)
    val s2: Try[Int] = Success(2)
    val _            = assert(mObj.unit(()).isFailure)
    val _            = assert((mObj.multiply((s1, s2)): Try[Int]) === Success(1))
  }

  test("Try[Int] satisfies Monoid left identity law") {
    val _ = assert(tryAdditive.MonoidLaws.leftIdentity)
  }

  test("Try[Int] satisfies Monoid right identity law") {
    val _ = assert(tryAdditive.MonoidLaws.rightIdentity)
  }

  test("Try[Int] satisfies Monoid associativity law") {
    val _ = assert(tryAdditive.MonoidLaws.associativity)
  }

  // =========================================================================
  // Function Additive & Monoid Object
  // =========================================================================

  private val functionAdditive = Monoid.Additive[Int => Option[String]]

  test("Function[Int, Option[String]] has Monoid.Additive instance") {
    val zeroFn = functionAdditive.zero
    val _      = assert(zeroFn(42) === None)
  }

  test("Function[Int, Option[String]] conforms to internal Monoid object") {
    val mObj = functionAdditive
    val u    = mObj.unit(())
    val _    = assert(u(42) === None)
  }

  test("Function[Int, Option[String]] satisfies Monoid left identity law") {
    val _ = assert(functionAdditive.MonoidLaws.leftIdentity)
  }

  test("Function[Int, Option[String]] satisfies Monoid right identity law") {
    val _ = assert(functionAdditive.MonoidLaws.rightIdentity)
  }

  test("Function[Int, Option[String]] satisfies Monoid associativity law") {
    val _ = assert(functionAdditive.MonoidLaws.associativity)
  }

  // =========================================================================
  // Multiplicative & Monoid Object (Int Product & Function)
  // =========================================================================

  private val intMultiplicative = Monoid.Multiplicative[Int]

  test("Int Product has Monoid.Multiplicative instance") {
    val _ = assert(intMultiplicative.one == 1)
    val _ = assert(intMultiplicative.times(3, 4) == 12)
    val _ = assert((3 * 4) == 12)
  }

  test("Int Product conforms to internal Monoid object") {
    val mObj = intMultiplicative
    val _    = assert(mObj.unit(()) == 1)
    val _    = assert(mObj.multiply((3, 4)) == 12)
  }

  test("Int Product satisfies Monoid left identity law") {
    val _ = assert(intMultiplicative.MonoidLaws.leftIdentity)
  }

  test("Int Product satisfies Monoid right identity law") {
    val _ = assert(intMultiplicative.MonoidLaws.rightIdentity)
  }

  test("Int Product satisfies Monoid associativity law") {
    val _ = assert(intMultiplicative.MonoidLaws.associativity)
  }

  test("Function[Int, Int] has Monoid.Multiplicative instance") {
    val fnMult = Monoid.Multiplicative[Int => Int]
    val oneFn  = fnMult.one
    val _      = assert(oneFn(42) == 1)

    val mObj = fnMult
    val u    = mObj.unit(())
    val _    = assert(u(42) == 1)

    val f: Int => Int = _ + 1
    val g: Int => Int = _ * 2
    val prod          = mObj.multiply((f, g))
    val _             = assert(prod(3) == 4 * 6)
  }
}
