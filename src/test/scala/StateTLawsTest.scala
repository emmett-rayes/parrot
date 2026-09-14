package parrot

import org.scalacheck.Arbitrary
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

import scala.annotation.targetName
import scala.util.{Failure, Success, Try}

class StateTLawsTest extends AnyFunSuite with ScalaCheckPropertyChecks {

  import StateT.given

  private val M  = Monad[StateT[String, Try]]
  private val RM = StateT.StateTIsRestrictionMonad[String, Try]
  private val MP = StateT.StateTIsMonoidPlus[String, Try]

  import MP.+
  import RM.{flatMap, restrict}

  // --- Observational Equivalence Helpers ---

  extension [B](t1: Try[(result: B, state: String)])
    @targetName("eqResult")
    infix def ===(t2: Try[(result: B, state: String)]): Boolean = (t1, t2) match {
      case (Success(s1), Success(s2)) => s1.result == s2.result && s1.state == s2.state
      case (Failure(e1), Failure(e2)) => e1.getMessage == e2.getMessage
      case _                          => false
    }

  extension [B](t1: Try[(result: B, state: String)])
    // Equivalence up to failure identification
    @targetName("eqResultFailureNorm")
    infix def =~=(t2: Try[(result: B, state: String)]): Boolean = (t1, t2) match {
      case (Success(s1), Success(s2)) => s1.result == s2.result && s1.state == s2.state
      case (Failure(_), Failure(_))   => true
      case _                          => false
    }

  // =========================================================================
  // Monad Laws on StateT
  // =========================================================================

  test("StateT: Monad left unitality") {
    val f: Int => StateT[String, Try][String] = {
      x => state => Success((result = x.toString, state = state))
    }
    forAll { (st: String) =>
      assert(M.unit(42).flatMap(f)(st) === f(42)(st))
    }
  }

  test("StateT: Monad right unitality") {
    val s: StateT[String, Try][Int] = {
      state => Success((result = 42, state = state))
    }
    forAll { (st: String) =>
      assert(s.flatMap(M.unit)(st) === s(st))
    }
  }

  // =========================================================================
  // MonoidPlus Laws on StateT
  // =========================================================================

  test("StateT: MonoidPlus left identity") {
    val s: StateT[String, Try][Int] = {
      state => Success((result = 42, state = state))
    }
    forAll { (st: String) =>
      assert((MP.zero[Int] + s)(st) === s(st))
    }
  }

  test("StateT: MonoidPlus right identity (up to failure equivalence)") {
    val s: StateT[String, Try][Int] = {
      state => Success((result = 42, state = state))
    }
    forAll { (st: String) =>
      assert((s + MP.zero[Int])(st) =~= s(st))
    }
  }

  // =========================================================================
  // RestrictionMonad Laws on StateT
  // =========================================================================

  test("StateT: RestrictionMonad idempotence") {
    val s: StateT[String, Try][Int] = {
      state => Success((result = 42, state = state))
    }
    forAll { (st: String) =>
      assert(s.restrict.restrict(st) === s.restrict(st))
    }
  }

  test("StateT: RestrictionMonad left absorption") {
    val s: StateT[String, Try][Int] = {
      state =>
        if state.nonEmpty then Success((result = 42, state = state.drop(1)))
        else Failure(Exception("empty state"))
    }
    forAll { (st: String) =>
      assert(s.restrict.flatMap(_ => s)(st) === s(st))
    }
  }

  test("StateT: RestrictionMonad commutativity (up to failure equivalence)") {
    val s1: StateT[String, Try][Int] = {
      state =>
        if state.startsWith("a") then Success((result = 1, state = state.drop(1)))
        else Failure(Exception("expected a"))
    }
    val s2: StateT[String, Try][String] = {
      state =>
        if state.startsWith("b") then Success((result = "b", state = state.drop(1)))
        else Failure(Exception("expected b"))
    }
    forAll { (st: String) =>
      val lhs = s1.restrict.flatMap(_ => s2.restrict)
      val rhs = s2.restrict.flatMap(_ => s1.restrict)
      assert(lhs(st) =~= rhs(st))
    }
  }
}
