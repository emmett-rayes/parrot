package parrot
package parser

import category.*

import org.scalacheck.{Arbitrary, Gen, Prop, Test}
import org.scalatest.funsuite.AnyFunSuite

import scala.util.{Failure, Success}

class ReferenceParserTest extends AnyFunSuite with ReferenceParser {

  given CanEqual[Any, Any] = CanEqual.derived

  private val inputs = Gen.oneOf("", "a", "b", "ab", "ba", "aa", "aab", "abab", "aaab", "a,a,a", "(a)", "((a))")

  /** Extensional equality of parsers: equal results on sampled semantic inputs and sources. */
  given ParserIsEq: [A: Arbitrary, B: Eq] => P[A, B] is Eq = new (P[A, B] is Eq) {
    def eq(p: P[A, B], q: P[A, B]): Boolean = {
      val prop = Prop.forAll(Arbitrary.arbitrary[A], inputs) { (a, source) =>
        (p(a)(Input(source, 0)), q(a)(Input(source, 0))) match {
          case (Success((result = x, state = i)), Success((result = y, state = j))) =>
            x === y && i.offset == j.offset
          case (Failure(_), Failure(_)) => true
          case _                        => false
        }
      }
      Test.check(Test.Parameters.default, prop).passed
    }
  }

  private val a      = literal("a")
  private val b      = literal("b")
  private val as     = regex("a+".r)
  private val digits = regex("[0-9]+".r)

  // =========================================================================
  // Primitives and derived combinators
  // =========================================================================

  test("literal and regex consume a prefix") {
    val _ = assert(a.parse("ab").get == (result = "a", offset = 1))
    val _ = assert(as.parse("aab").get == (result = "aa", offset = 2))
    val _ = assert(digits.parse("123abc").get == (result = "123", offset = 3))
    val _ = assert(b.parse("ab").isFailure)
  }

  test("sequencing and skipThen / thenSkip") {
    val ab    = (a *> b)
    val _     = assert(ab.parse("ab").get == (result = "b", offset = 2))
    val aOnly = (a <* b)
    val _     = assert(aOnly.parse("ab").get == (result = "a", offset = 2))
    val _     = assert(as.between(literal("("), literal(")")).parse("(aa)").get == (result = "aa", offset = 4))
  }

  test("pairing and map") {
    val pair = (a && b).map((x, y) => s"$x+$y")
    val _    = assert(pair.parse("ab").get == (result = "a+b", offset = 2))
    val _    = assert((a && b).parse("ab").get == (result = ("a", "b"), offset = 2))
  }

  test("choice and alternation") {
    val either = a |> b

    val _ = assert(either.parse("a").get == (result = "a", offset = 1))
    val _ = assert(either.parse("b").get == (result = "b", offset = 1))
    val _ = assert(either.parse("c").isFailure)
    val _ = assert((a +> b).parse("b").get == (result = Right("b"), offset = 1))
    val _ = assert(a.optional.parse("b").get == (result = Right(()), offset = 0))
    val _ =
      assert(((a +> b) >> (pure[String, Int](_.length) || pure(_ => 0))).parse("a").get == (result = 1, offset = 1))
  }

  test("lookahead and not") {
    val _          = assert((~a).parse("ab").get == (result = (), offset = 0))
    val _          = assert((!b).parse("ab").get == (result = (), offset = 0))
    val _          = assert((!a).parse("ab").isFailure)
    val pos        = ~a *> a
    val _          = assert(pos.parse("ab").get == (result = "a", offset = 1))
    val neg        = !b *> a
    val _          = assert(neg.parse("ab").get == (result = "a", offset = 1))
    val failingNeg = !a *> a
    val _          = assert(failingNeg.parse("ab").isFailure)
  }

  test("repeated, times, atLeast and separatedBy") {
    val rep = a.repeated

    val _ = assert(rep.parse("aaab").get == (result = Vector("a", "a", "a"), offset = 3))
    val _ = assert(rep.parse("b").get == (result = Vector.empty, offset = 0))
    val _ = assert(a.times(2).parse("aaa").get == (result = Vector("a", "a"), offset = 2))
    val _ = assert(a.times(2).parse("ab").isFailure)
    val _ = assert(a.atLeast(2).parse("aaab").get == (result = Vector("a", "a", "a"), offset = 3))
    val _ = assert(a.atLeast(2).parse("ab").isFailure)

    val sep = a.separatedBy(literal(","))
    val _   = assert(sep.parse("a,a,ab").get == (result = Vector("a", "a", "a"), offset = 5))
  }

  test("recursive parsing") {
    // nested ::= "(" nested ")" | "x"
    lazy val nested: P[Unit, String] = recursive[Unit, String] { self =>
      literal("(") *> self <* literal(")") |> literal("x")
    }
    val _ = assert(nested.parseAll("((x))").get == (result = "x", offset = 5))
    val _ = assert(nested.parseAll("((x)").isFailure)
  }

  test("recursive solves mutual recursion via Bekić's theorem") {
    // even ::= "a" odd | ""   odd ::= "a" even
    val (even, odd) = recursive[(P[Unit, Int], P[Unit, Int])] { case (even, odd) =>
      ((a *> odd).map(_ + 1) |> pure(_ => 0), (a *> even).map(_ + 1))
    }
    val _ = assert(even.parseAll("aaaa").get == (result = 4, offset = 4))
    val _ = assert(odd.parseAll("aaa").get == (result = 3, offset = 3))
    val _ = assert(even.parseAll("aaa").isFailure)
  }

  test("parseAll validates end of input") {
    val _ = assert(a.parseAll("a").get == (result = "a", offset = 1))
    val _ = assert(a.parseAll("ab").isFailure)
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
