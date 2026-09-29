package parrot
package category

import org.scalacheck.{Arbitrary, Gen}

import scala.util.{Failure, Success, Try}

class MonoidTest extends CategorySuite {

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
    assert((none + none) === None)
  }

  test("Option[Int] conforms to internal Monoid object") {
    val mObj = optionAdditive
    val _    = assert((mObj.unit(()): Option[Int]) === None)
    val _    = assert((mObj.multiply((Some(1), Some(2))): Option[Int]) === Some(1))
    val _    = assert((mObj.multiply((None, Some(2))): Option[Int]) === Some(2))
    assert((mObj.multiply((None, None)): Option[Int]) === None)
  }

  test("Option[Int] satisfies Monoid left identity law") {
    assert(optionAdditive.MonoidLaws.leftIdentity)
  }

  test("Option[Int] satisfies Monoid right identity law") {
    assert(optionAdditive.MonoidLaws.rightIdentity)
  }

  test("Option[Int] satisfies Monoid associativity law") {
    assert(optionAdditive.MonoidLaws.associativity)
  }

  // =========================================================================
  // Try[Int] Additive & Monoid Object (Quotient Equality on Errors)
  // =========================================================================

  private val tryAdditive = Monoid.Additive[Try[Int]]

  test("Try[Int] has Monoid.Additive instance") {
    import tryAdditive.+
    val s1: Try[Int]    = Success(1)
    val s2: Try[Int]    = Success(2)
    val fErr1: Try[Int] = Failure(new IllegalArgumentException("arg"))
    val fErr2: Try[Int] = Failure(new NoSuchElementException("element"))

    val _ = assert(tryAdditive.zero.isFailure)
    val _ = assert((s1 + s2) === Success(1))
    val _ = assert((fErr1 + s2) === Success(2))
    // Verifies quotient equivalence where distinct failures are identified
    assert(Eq[Try[Int]].eq(fErr1 + fErr2, tryAdditive.zero))
  }

  test("Try[Int] conforms to internal Monoid object") {
    val mObj         = tryAdditive
    val s1: Try[Int] = Success(1)
    val s2: Try[Int] = Success(2)
    val _            = assert(mObj.unit(()).isFailure)
    val _            = assert((mObj.multiply((s1, s2)): Try[Int]) === Success(1))
    assert((mObj.multiply((Failure(new RuntimeException("err")), s2)): Try[Int]) === Success(2))
  }

  test("Try[Int] satisfies Monoid left identity law") {
    assert(tryAdditive.MonoidLaws.leftIdentity)
  }

  test("Try[Int] satisfies Monoid right identity law") {
    assert(tryAdditive.MonoidLaws.rightIdentity)
  }

  test("Try[Int] satisfies Monoid associativity law") {
    assert(tryAdditive.MonoidLaws.associativity)
  }

  // =========================================================================
  // Set[Int] Additive & Monoid Object (Commutative Enrichment)
  // =========================================================================

  private val setAdditive = Monoid.Additive[Set[Int]]

  test("Set[Int] has Monoid.Additive instance") {
    import setAdditive.+
    val s1 = Set(1, 2)
    val s2 = Set(2, 3)
    val _  = assert(setAdditive.zero === Set.empty[Int])
    val _  = assert(setAdditive.plus(s1, s2) === Set(1, 2, 3))
    val _  = assert((s1 + s2) === Set(1, 2, 3))
    assert((setAdditive.zero + s1) === s1)
  }

  test("Set[Int] conforms to internal Monoid object") {
    val mObj = setAdditive
    val s1   = Set(1, 2)
    val s2   = Set(3, 4)
    val _    = assert((mObj.unit(()): Set[Int]) === Set.empty[Int])
    assert((mObj.multiply((s1, s2)): Set[Int]) === Set(1, 2, 3, 4))
  }

  test("Set[Int] satisfies Monoid left identity law") {
    assert(setAdditive.MonoidLaws.leftIdentity)
  }

  test("Set[Int] satisfies Monoid right identity law") {
    assert(setAdditive.MonoidLaws.rightIdentity)
  }

  test("Set[Int] satisfies Monoid associativity law") {
    assert(setAdditive.MonoidLaws.associativity)
  }

  // =========================================================================
  // Function Additive & Monoid Object
  // =========================================================================

  private def functionAdditive = Monoid.Additive[Int => Option[String]]

  given arbIntOptStr: Arbitrary[Int => Option[String]] = Arbitrary {
    Gen.oneOf(
      Gen.const((i: Int) => if i > 0 then Some(s"pos:$i") else None),
      Gen.const((i: Int) => if i % 2 == 0 then Some(s"even:$i") else None),
      Gen.const((i: Int) => if i == 0 then Some("zero") else None),
      Gen.const((i: Int) => Some(s"all:$i")),
      Gen.const((_: Int) => None),
    )
  }

  test("Function[Int, Option[String]] has Monoid.Additive instance") {
    val zeroFn = functionAdditive.zero
    val _      = assert(zeroFn(42) === None)
    assert(zeroFn(-1) === None)
  }

  test("Function[Int, Option[String]] conforms to internal Monoid object") {
    val mObj = functionAdditive
    val u    = mObj.unit(())
    assert(u(42) === None)
  }

  test("Function[Int, Option[String]] satisfies Monoid left identity law") {
    assert(functionAdditive.MonoidLaws.leftIdentity)
  }

  test("Function[Int, Option[String]] satisfies Monoid right identity law") {
    assert(functionAdditive.MonoidLaws.rightIdentity)
  }

  test("Function[Int, Option[String]] satisfies Monoid associativity law") {
    assert(functionAdditive.MonoidLaws.associativity)
  }

  // =========================================================================
  // Multiplicative & Monoid Object (Int Product & Function)
  // =========================================================================

  private val intMultiplicative = Monoid.Multiplicative[Int]

  test("Int Product has Monoid.Multiplicative instance") {
    import intMultiplicative.*
    val _ = assert(intMultiplicative.one === 1)
    val _ = assert(intMultiplicative.times(3, 4) === 12)
    val _ = assert((3 * 4) === 12)
    assert((1 * 5) === 5)
  }

  test("Int Product conforms to internal Monoid object") {
    val mObj = intMultiplicative
    val _    = assert((mObj.unit(()): Int) === 1)
    assert((mObj.multiply((3, 4)): Int) === 12)
  }

  test("Int Product satisfies Monoid left identity law") {
    assert(intMultiplicative.MonoidLaws.leftIdentity)
  }

  test("Int Product satisfies Monoid right identity law") {
    assert(intMultiplicative.MonoidLaws.rightIdentity)
  }

  test("Int Product satisfies Monoid associativity law") {
    assert(intMultiplicative.MonoidLaws.associativity)
  }

  private val functionMultiplicative = Monoid.Multiplicative[Int => Int]

  test("Function[Int, Int] has Monoid.Multiplicative instance") {
    val oneFn = functionMultiplicative.one
    val _     = assert(oneFn(42) === 1)
    assert(oneFn(-10) === 1)
  }
}
