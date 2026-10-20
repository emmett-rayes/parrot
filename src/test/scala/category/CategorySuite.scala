package parrot
package category

import org.scalacheck.*
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

import scala.util.{Failure, Success, Try}

/** Shared base test suite for category law checking with sharp generators and function equality. */
abstract class CategorySuite extends AnyFunSuite with ScalaCheckPropertyChecks {

  /** Extensional equality for functions into type equality proofs. */
  given TypeEqFunctionIsEq: [A, B, C] => Function[A, B =:= C] is Eq =
    new (Function[A, B =:= C] is Eq) {
      def eq(f: A => (B =:= C), g: A => (B =:= C)): Boolean = {
        true
      }
    }

  /** Extensional equality for functions using ScalaCheck sampling. */
  given ArbitraryFunctionIsEq: [A, B] => (arbA: Arbitrary[A], eqB: B is Eq) => Function[A, B] is Eq =
    new (Function[A, B] is Eq) {
      def eq(f: A => B, g: A => B): Boolean = {
        val prop = Prop.forAll((a: A) => f(a) === g(a))
        Test.check(Test.Parameters.default, prop).passed
      }
    }

  /** Sharp generator for `Try[A]` covering varied successes and multiple distinct failure exceptions. */
  given ArbitraryTry: [A: Arbitrary] => Arbitrary[Try[A]] = Arbitrary {
    Gen.oneOf(
      Arbitrary.arbitrary[A].map(Success(_)),
      Gen.const(Failure(new IllegalArgumentException("invalid argument"))),
      Gen.const(Failure(new NoSuchElementException("element not found"))),
      Gen.const(Failure(new RuntimeException("standard runtime error"))),
      Gen.const(Failure(new Exception("generic checked exception"))),
    )
  }

  /** Sharp generator for `Option[A]` covering boundary values and `None`. */
  given ArbitraryOption: [A: Arbitrary] => Arbitrary[Option[A]] = Arbitrary {
    Gen.oneOf(
      Arbitrary.arbitrary[A].map(Some(_)),
      Gen.const(None),
    )
  }

  /** Sharp generator for `Set[A]` covering empty, singleton, and multi-element sets. */
  given ArbitrarySet: [A: Arbitrary] => Arbitrary[Set[A]] = Arbitrary {
    for {
      n     <- Gen.choose(0, 4)
      elems <- Gen.listOfN(n, Arbitrary.arbitrary[A])
    } yield elems.toSet
  }

  /** Sharp generator for `LazyTuple2[A, B]`. */
  given ArbitraryLazyTuple2: [A: Arbitrary, B: Arbitrary] => Arbitrary[LazyTuple2[A, B]] = Arbitrary {
    for {
      a <- Arbitrary.arbitrary[A]
      b <- Arbitrary.arbitrary[B]
    } yield LazyTuple2(a, b)
  }
}
