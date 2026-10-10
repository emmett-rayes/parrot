package parrot
package parser

import parrot.category.Eq

import org.scalacheck.{Arbitrary, Gen, Prop, Test}
import org.scalatest.funsuite.AnyFunSuite

class ReferenceParserTest extends AnyFunSuite {
  import ReferenceParser.*
  import ReferenceParser.Result.{Failure, Success}

  given CanEqual[Unit, Unit] = CanEqual.derived

  private val inputs = Gen.oneOf("", "a", "b", "ab", "ba", "aa", "aab", "abab", "aaab", "a,a,a", "(a)", "((a))")

  /** Extensional equality of parsers: equal results on sampled semantic inputs and sources. */
  given ParserIsEq: [A: Arbitrary, B: Eq] => P[A, B] is Eq = new (P[A, B] is Eq) {
    def eq(p: P[A, B], q: P[A, B]): Boolean = {
      val prop = Prop.forAll(Arbitrary.arbitrary[A], inputs) { (a, source) =>
        (p(a)(Input(source, 0)), q(a)(Input(source, 0))) match {
          case (Success(x, i), Success(y, j)) => x === y && i == j
          case (Failure(_, _), Failure(_, _)) => true
          case _                              => false
        }
      }
      Test.check(Test.Parameters.default, prop).passed
    }
  }

  private val a  = literal("a")
  private val b  = literal("b")
  private val as = regex("a+".r)

  // =========================================================================
  // Primitives and derived combinators
  // =========================================================================

  test("literal and regex consume a prefix") {
    val _ = assert(a.parse("ab") == Success("a", 1))
    val _ = assert(as.parse("aab") == Success("aa", 2))
    val _ = assert(b.parse("ab") == Failure(0, "\"b\""))
  }

  test("pair, skipThen, thenSkip and between share the semantic input") {
    val _ = assert((a && b).parse("ab") == Success(("a", "b"), 2))
    val _ = assert((a *> b).parse("ab") == Success("b", 2))
    val _ = assert((a <* b).parse("ab") == Success("a", 2))
    val _ = assert(as.between(literal("("), literal(")")).parse("(aa)") == Success("aa", 4))
  }

  test("or, optional and merge tag and dispatch on branches") {
    val _ = assert((a +> b).parse("b") == Success(Right("b"), 1))
    val _ = assert(a.optional.parse("b") == Success(Right(()), 0))
    val _ = assert(((a +> b) >> (pure[String, Int](_.length) || pure(_ => 0))).parse("a") == Success(1, 1))
  }

  test("lookahead and not consume no input") {
    val _ = assert((~a).parse("ab") == Success((), 0))
    val _ = assert((!b).parse("ab") == Success((), 0))
    val _ = assert((!a).parse("ab").isInstanceOf[Failure])
  }

  test("repeated, times, atLeast and separatedBy collect results") {
    val _ = assert(a.repeated.parse("aab") == Success(Vector("a", "a"), 2))
    val _ = assert(a.repeated.parse("b") == Success(Vector(), 0))
    val _ = assert(a.times(2).parse("aaa") == Success(Vector("a", "a"), 2))
    val _ = assert(a.times(2).parse("ab").isInstanceOf[Failure])
    val _ = assert(a.atLeast(2).parse("aaab") == Success(Vector("a", "a", "a"), 3))
    val _ = assert(a.atLeast(2).parse("ab").isInstanceOf[Failure])
    val _ = assert(a.separatedBy(literal(",")).parse("a,a,a,") == Success(Vector("a", "a", "a"), 5))
  }

  test("recursive computes fixed points") {
    val nested = recursive[Unit, String](self => a |> self.between(literal("("), literal(")")))
    val _ = assert(nested.parseAll("((a))") == Success("a", 5))
    val _ = assert(nested.parseAll("((a)").isInstanceOf[Failure])
  }

  test("recursive solves mutual recursion via Bekić's theorem") {
    // even ::= "a" odd | ""   odd ::= "a" even
    val (even, odd) = recursive[(P[Unit, Int], P[Unit, Int])] { case (even, odd) =>
      ((a *> odd).map(_ + 1) |> pure(_ => 0), (a *> even).map(_ + 1))
    }
    val _ = assert(even.parseAll("aaaa") == Success(4, 4))
    val _ = assert(odd.parseAll("aaa") == Success(3, 3))
    val _ = assert(even.parseAll("aaa").isInstanceOf[Failure])
  }

  // =========================================================================
  // Laws
  // =========================================================================

  private val laws = ParserLaws

  private val samples: List[P[Unit, String]] = List(a, b, as, a *> b, a |> b, a.repeated.map(_.mkString), failure)

  private val countdown: P[Int, Either[Int, Int]] = {
    a.mapInput((_: Int) => ()).pair(success[Int]).map((_, n) => if n <= 0 then Left(n) else Right(n - 1)) |>
      pure(n => Left(-n))
  }

  test("ParserLaws: category") {
    for p <- samples; q <- samples do {
      val _ = assert(laws.leftIdentity(p))
      val _ = assert(laws.rightIdentity(p))
      val _ = assert(laws.associativity(p.map(_ => ()), q.map(_ => ()), p))
    }
    val _ = assert(laws.zipIdentity[Unit, Int])
  }

  test("ParserLaws: zeros and choice monoid") {
    for p <- samples; q <- samples do {
      val _ = assert(laws.leftZero[Unit, Unit, String](p))
      val _ = assert(laws.rightZero[Unit, String, Int](p))
      val _ = assert(laws.choiceLeftIdentity(p))
      val _ = assert(laws.choiceRightIdentity(p))
      val _ = assert(laws.choiceAssociativity(p, q, a))
    }
  }

  test("ParserLaws: lookahead is a restriction, not is its complement") {
    for p <- samples; q <- samples do {
      val _ = assert(laws.lookaheadIdentity(p))
      val _ = assert(laws.lookaheadCommutativity(p, q))
      val _ = assert(laws.lookaheadCompose(p, q))
      val _ = assert(laws.lookaheadPrecompose(p, regex(".*".r).mapInput((_: String) => ())))
      val _ = assert(laws.doubleNegation(p))
      val _ = assert(laws.negationExclusion(p))
    }
  }

  test("ParserLaws: loop unfolds") {
    val _ = assert(laws.loopUnfolding(countdown))
  }

  test("ParserLaws: recursion unfolds") {
    val nested: P[Unit, String] => P[Unit, String] = self => a |> self.between(literal("("), literal(")"))
    val _ = assert(laws.recursionUnfolding(nested))
  }
}
