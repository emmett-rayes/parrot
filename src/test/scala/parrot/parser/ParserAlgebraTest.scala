package parrot
package parser

import category.*
import org.scalacheck.Gen

import Sample.given

/** A grammar in which what a parser consumes depends on an earlier result: a length, then that many characters. */
final class LengthPrefixed(tracked val algebra: ParserAlgebra) extends caps.Pure {
  import algebra.*

  private type State = (BigInt, String)

  private val length    = regex("[0-9]+".r).map(lift[String, BigInt](BigInt(_)))
  private val char      = regex("[a-z]".r).mapInput(lift[State, Unit](_ => ()))
  private val start     = lift[BigInt, State]((_, ""))
  private val countdown = lift[State, Either[String, State]]((n, s) => if n > 0 then Right((n - 1, s)) else Left(s))
  private val append    = lift[(State, String), State] { case ((n, s), c) => (n, s + c) }
  private val step      = pure(countdown) >> (success[String] ++ (success[State] && char).map(append))

  /** The characters of a length-prefixed string. */
  val string: P[Unit, String] = length.map(start) >> step.iterate
}

/** The grammar of sums of products, as a family of three rules: each rule begins with a call of the next one, and the
  * last calls the first after an opening parenthesis, so the family has no left recursion.
  */
final class Arithmetic(tracked val algebra: ParserAlgebra) extends caps.Pure {
  import algebra.*

  private val number = regex("[0-9]+".r).map(lift[String, Int](_.toInt))

  /** The value of an expression. */
  val expression: P[Unit, Int] = {
    recursive[(P[Unit, Int], P[Unit, Int], P[Unit, Int])] { (expression, term, factor) =>
      (
        term.separatedBy(literal("+")).map(lift[Vector[Int], Int](_.sum)),
        factor.separatedBy(literal("*")).map(lift[Vector[Int], Int](_.product)),
        number |> expression.between(literal("("), literal(")")),
      )
    }._1
  }
}

/** A rule whose recursive call follows a lookahead, which consumes nothing: the call is unguarded. */
final class LookaheadRecursion(tracked val algebra: ParserAlgebra) extends caps.Pure {
  import algebra.*

  /** An "a", after a failed call of the rule itself. */
  val rule: P[Unit, String] = recursive[Unit, String](self => (~literal("a") >> self) |> literal("a"))
}

/** The equations of parsing expression grammars, on random grammars, for an interpreter. */
abstract class ParserLawSpec(name: String, tracked val semantics: Semantics) extends LawSuite("PEG", name) {
  export semantics.algebra
  import algebra.*
  import algebra.ParserLaws.*

  private lazy val parsers: Gen[P[Int, Int]]                = Grammars.terms.map(Grammars.interpret(algebra))
  private lazy val observe: Gen[P[Int, Int] is Observable]  = ParserGen.exact[Int, Int](semantics)
  private lazy val semantic: Gen[P[Int, Int] is Observable] = ParserGen.observe[Int, Int](semantics)
  private lazy val order: Gen[P[Int, Int] is Preorder]      = ParserGen.order[Int, Int](semantics)

  /** A parser and one that reports at least as much: where *p* fails, it also runs *q* and fails. */
  private lazy val refined: Gen[(P[Int, Int], P[Int, Int])] = {
    Gen.zip(parsers, parsers).map((p, q) => (p, p |> (q >> failure[Int, Int])))
  }
  private lazy val steps: Gen[P[Int, Either[Int, Int]]]   = Grammars.terms.map(Grammars.step(algebra))

  /** A guarded step and one that reports at least as much: where the step fails, it also runs *q* and fails. */
  private lazy val refinedSteps: Gen[(P[Int, Either[Int, Int]], P[Int, Either[Int, Int]])] = {
    Gen.zip(steps, parsers).map((p, q) => (p, p |> (q >> failure[Int, Either[Int, Int]])))
  }
  private lazy val rules: Gen[P[Int, Int] -> P[Int, Int]] = Grammars.terms.map(Grammars.nest(algebra))
  private lazy val consuming: Gen[P[Int, Int]]            = parsers.map(p => Grammars.consume(algebra)("a") >> p)

  law("leftIdentity") {
    forAll(observe, parsers) { (o, p) =>
      given (P[Int, Int] is Observable) = o
      leftIdentity(p)
    }
  }

  law("rightIdentity") {
    forAll(observe, parsers) { (o, p) =>
      given (P[Int, Int] is Observable) = o
      rightIdentity(p)
    }
  }

  law("associativity") {
    forAll(observe, parsers, parsers, parsers) { (o, p, q, r) =>
      given (P[Int, Int] is Observable) = o
      associativity(p, q, r)
    }
  }

  law("zipIdentity") {
    forAll(ParserGen.exact[(Int, Int), (Int, Int)](semantics)) { o =>
      given (P[(Int, Int), (Int, Int)] is Observable) = o
      zipIdentity[Int, Int]
    }
  }

  law("zipDefinition") {
    forAll(ParserGen.exact[(Int, Int), (Int, Int)](semantics), parsers, parsers) { (o, p, q) =>
      given (P[(Int, Int), (Int, Int)] is Observable) = o
      zipDefinition(p, q)
    }
  }

  law("branchDefinition") {
    forAll(ParserGen.exact[Either[Int, Int], Either[Int, Int]](semantics), parsers, parsers) { (o, p, q) =>
      given (P[Either[Int, Int], Either[Int, Int]] is Observable) = o
      branchDefinition(p, q)
    }
  }

  law("mapDefinition") {
    forAll(observe, parsers, Sample.function[Int, Int]) { (o, p, g) =>
      given (P[Int, Int] is Observable) = o
      mapDefinition(p, lift(g))
    }
  }

  law("mapInputDefinition") {
    forAll(observe, parsers, Sample.function[Int, Int]) { (o, p, f) =>
      given (P[Int, Int] is Observable) = o
      mapInputDefinition(p, lift(f))
    }
  }

  law("mergeDefinition") {
    forAll(ParserGen.exact[Either[Int, Int], Int](semantics), parsers, parsers) { (o, p, q) =>
      given (P[Either[Int, Int], Int] is Observable) = o
      mergeDefinition(p, q)
    }
  }

  law("orDefinition") {
    forAll(ParserGen.exact[Int, Either[Int, Int]](semantics), parsers, parsers) { (o, p, q) =>
      given (P[Int, Either[Int, Int]] is Observable) = o
      orDefinition(p, q)
    }
  }

  law("pairDefinition") {
    forAll(ParserGen.exact[Int, (Int, Int)](semantics), parsers, parsers) { (o, p, q) =>
      given (P[Int, (Int, Int)] is Observable) = o
      pairDefinition(p, q)
    }
  }

  law("skipThenDefinition") {
    forAll(observe, parsers, parsers) { (o, p, q) =>
      given (P[Int, Int] is Observable) = o
      skipThenDefinition(p, q)
    }
  }

  law("thenSkipDefinition") {
    forAll(observe, parsers, parsers) { (o, p, q) =>
      given (P[Int, Int] is Observable) = o
      thenSkipDefinition(p, q)
    }
  }

  law("betweenDefinition") {
    forAll(observe, parsers, parsers, parsers) { (o, p, open, close) =>
      given (P[Int, Int] is Observable) = o
      betweenDefinition(p, open, close)
    }
  }

  law("leftZero") {
    forAll(observe, parsers) { (o, p) =>
      given (P[Int, Int] is Observable) = o
      leftZero[Int, Int, Int](p)
    }
  }

  law("rightZero", "inequation: diagnostics of p are kept") {
    forAll(order, parsers) { (o, p) =>
      given (P[Int, Int] is Preorder) = o
      rightZero[Int, Int, Int](p)
    }
  }

  law("choiceIdentity") {
    forAll(observe, parsers) { (o, p) =>
      given (P[Int, Int] is Observable) = o
      choiceIdentity(p)
    }
  }

  law("choiceAssociativity") {
    forAll(observe, parsers, parsers, parsers) { (o, p, q, r) =>
      given (P[Int, Int] is Observable) = o
      choiceAssociativity(p, q, r)
    }
  }

  law("choicePrecomposition") {
    forAll(observe, parsers, parsers, parsers) { (o, h, p, q) =>
      given (P[Int, Int] is Observable) = o
      choicePrecomposition(h, p, q)
    }
  }

  law("attemptDefinition") {
    forAll(ParserGen.exact[Int, Either[Int, Int]](semantics), parsers) { (o, p) =>
      given (P[Int, Either[Int, Int]] is Observable) = o
      attemptDefinition(p)
    }
  }

  law("choiceByAttempt") {
    forAll(observe, parsers, parsers) { (o, p, q) =>
      given (P[Int, Int] is Observable) = o
      choiceByAttempt(p, q)
    }
  }

  law("lookaheadIdentity", "inequation: lookahead is silent") {
    forAll(order, parsers) { (o, p) =>
      given (P[Int, Int] is Preorder) = o
      lookaheadIdentity(p)
    }
  }

  law("lookaheadCommutativity") {
    forAll(observe, parsers, parsers) { (o, p, q) =>
      given (P[Int, Int] is Observable) = o
      lookaheadCommutativity(p, q)
    }
  }

  law("lookaheadCompose") {
    forAll(observe, parsers, parsers) { (o, p, q) =>
      given (P[Int, Int] is Observable) = o
      lookaheadCompose(p, q)
    }
  }

  law("lookaheadPrecompose", "inequation: lookahead is silent") {
    forAll(order, parsers, parsers) { (o, p, q) =>
      given (P[Int, Int] is Preorder) = o
      lookaheadPrecompose(p, q)
    }
  }

  law("doubleNegation") {
    forAll(observe, parsers) { (o, p) =>
      given (P[Int, Int] is Observable) = o
      doubleNegation(p)
    }
  }

  law("negationExclusion") {
    forAll(observe, parsers) { (o, p) =>
      given (P[Int, Int] is Observable) = o
      negationExclusion(p)
    }
  }

  law("negationCover") {
    forAll(observe, parsers) { (o, p) =>
      given (P[Int, Int] is Observable) = o
      negationCover(p)
    }
  }

  law("loopUnfolding", "guarded steps") {
    forAll(observe, steps) { (o, p) =>
      given (P[Int, Int] is Observable) = o
      loopUnfolding(p)
    }
  }

  law("recursionUnfolding", "guarded rules") {
    forAll(observe, rules) { (o, f) =>
      given (P[Int, Int] is Observable) = o
      recursionUnfolding(f)
    }
  }

  law("repeatedUnfolding", "parsers that consume") {
    forAll(ParserGen.exact[Int, Vector[Int]](semantics), consuming) { (o, p) =>
      given (P[Int, Vector[Int]] is Observable) = o
      repeatedUnfolding(p)
    }
  }

  law("atLeastOnceDefinition") {
    forAll(ParserGen.exact[Int, Vector[Int]](semantics), parsers) { (o, p) =>
      given (P[Int, Vector[Int]] is Observable) = o
      atLeastOnceDefinition(p)
    }
  }

  law("repeatedDefinition") {
    forAll(ParserGen.exact[Int, Vector[Int]](semantics), parsers) { (o, p) =>
      given (P[Int, Vector[Int]] is Observable) = o
      repeatedDefinition(p)
    }
  }

  law("timesDefinition") {
    forAll(ParserGen.exact[Int, Vector[Int]](semantics), parsers, Gen.choose(0, 3)) { (o, p, n) =>
      given (P[Int, Vector[Int]] is Observable) = o
      timesDefinition(p, n)
    }
  }

  law("atLeastDefinition") {
    forAll(ParserGen.exact[Int, Vector[Int]](semantics), parsers, Gen.choose(0, 3)) { (o, p, n) =>
      given (P[Int, Vector[Int]] is Observable) = o
      atLeastDefinition(p, n)
    }
  }

  law("separatedByDefinition") {
    forAll(ParserGen.exact[Int, Vector[Int]](semantics), parsers, parsers) { (o, p, separator) =>
      given (P[Int, Vector[Int]] is Observable) = o
      separatedByDefinition(p, separator)
    }
  }

  law("ruleTransparent", "without diagnostics") {
    forAll(semantic, parsers, Gen.oneOf("x", "y")) { (o, p, label) =>
      given (P[Int, Int] is Observable) = o
      ruleTransparent(p, label)
    }
  }

  law("andThenMonotone") {
    forAll(order, refined, refined) { case (o, (p, p2), (q, q2)) =>
      given (P[Int, Int] is Preorder) = o
      andThenMonotone(p, p2, q, q2)
    }
  }

  law("orElseMonotone") {
    forAll(order, refined, refined) { case (o, (p, p2), (q, q2)) =>
      given (P[Int, Int] is Preorder) = o
      orElseMonotone(p, p2, q, q2)
    }
  }

  law("zipMonotone") {
    forAll(ParserGen.order[(Int, Int), (Int, Int)](semantics), refined, refined) { case (o, (p, p2), (q, q2)) =>
      given (P[(Int, Int), (Int, Int)] is Preorder) = o
      zipMonotone(p, p2, q, q2)
    }
  }

  law("branchMonotone") {
    forAll(ParserGen.order[Either[Int, Int], Either[Int, Int]](semantics), refined, refined) {
      case (o, (p, p2), (q, q2)) =>
        given (P[Either[Int, Int], Either[Int, Int]] is Preorder) = o
        branchMonotone(p, p2, q, q2)
    }
  }

  law("iterateMonotone", "guarded steps") {
    forAll(order, refinedSteps) { case (o, (p, p2)) =>
      given (P[Int, Int] is Preorder) = o
      iterateMonotone(p, p2)
    }
  }

  law("attemptMonotone") {
    forAll(ParserGen.order[Int, Either[Int, Int]](semantics), refined) { case (o, (p, p2)) =>
      given (P[Int, Either[Int, Int]] is Preorder) = o
      attemptMonotone(p, p2)
    }
  }

  law("lookaheadMonotone") {
    forAll(order, refined) { case (o, (p, p2)) =>
      given (P[Int, Int] is Preorder) = o
      lookaheadMonotone(p, p2)
    }
  }

  law("notMonotone") {
    forAll(order, refined) { case (o, (p, p2)) =>
      given (P[Int, Int] is Preorder) = o
      notMonotone(p, p2)
    }
  }

  law("ruleMonotone") {
    forAll(order, refined, Gen.oneOf("x", "y")) { case (o, (p, p2), label) =>
      given (P[Int, Int] is Preorder) = o
      ruleMonotone(p, p2, label)
    }
  }

  counterexample("lookaheadIdentity", "exactly, with diagnostics: lookahead is silent") {
    forAll(observe, parsers) { (o, p) =>
      given (P[Int, Int] is Observable) = o
      (~p >> p) =?= p
    }
  }

  counterexample("choicePostcomposition", "ordered choice commits") {
    forAll(observe, parsers, parsers, parsers) { (o, p, q, h) =>
      given (P[Int, Int] is Observable) = o
      ((p |> q) >> h) =?= ((p >> h) |> (q >> h))
    }
  }

  test(s"$name: what a parser consumes can depend on an earlier result") {
    val string = LengthPrefixed(semantics.algebra).string

    val _ = assert(semantics.run(string)((), "3abc") == Some(("abc", 4)))
    val _ = assert(semantics.run(string)((), "2abc") == Some(("ab", 3)))
    val _ = assert(semantics.run(string)((), "0abc") == Some(("", 1)))
    val _ = assert(semantics.run(string)((), "10abcdefghij") == Some(("abcdefghij", 12)))
    assert(semantics.run(string)((), "3ab").isEmpty)
  }
}

class ReferenceParserLawTest extends ParserLawSpec("ReferenceParser", Interpreters.reference.Semantics)

class StrictParserLawTest extends ParserLawSpec("StrictParser", Interpreters.strict.Semantics)

/** The core invariant: on every grammar and at every position, the optimizing interpreter does what the reference does.
  */
class AgreementTest extends LawSuite("Agreement", "StrictParser") {
  import Interpreters.{reference, strict}

  law("results, offsets and diagnostics of ReferenceParser", "random grammars") {
    forAll(Grammars.terms, Grammars.inputs, Gen.choose(-5, 5)) { (term, in, n) =>
      val expected = reference.diagnose(Grammars.interpret(reference)(term))(n, in.source, in.offset)
      val actual   = strict.diagnose(Grammars.interpret(strict)(term))(n, in.source, in.offset)
      Eq.Tuple2IsEq(using Expected.ExpectedIsEq, Eq.OptionIsEq(using Eq.Tuple2IsEq(using Eq.IntIsEq, Eq.IntIsEq)))
        .equal(expected, actual)
    }
  }

  law("results and offsets without diagnostics", "random grammars") {
    forAll(Grammars.terms, Grammars.inputs, Gen.choose(-5, 5)) { (term, in, n) =>
      val expected = reference.run(Grammars.interpret(reference)(term))(n, in.source, in.offset)
      val actual   = strict.run(Grammars.interpret(strict)(term))(n, in.source, in.offset)
      Eq.OptionIsEq(using Eq.Tuple2IsEq(using Eq.IntIsEq, Eq.IntIsEq)).equal(expected, actual)
    }
  }

  law("totality", "random grammars with unguarded recursion") {
    forAll(Grammars.unguardedTerms, Grammars.inputs, Gen.choose(-5, 5)) { (term, in, n) =>
      AgreementTest.total(strict.Semantics)(term, in, n)
    }
  }

  law("parse and parseAll of ReferenceParser", "random grammars") {
    forAll(Grammars.terms, Grammars.sources, Gen.choose(-5, 5)) { (term, source, n) =>
      val slow     = AgreementTest.closed(reference)(term, n)
      val fast     = AgreementTest.closed(strict)(term, n)
      val outcomes = Eq.EitherIsEq(using Eq.StringIsEq, Eq.Tuple2IsEq(using Eq.IntIsEq, Eq.IntIsEq))
      outcomes.equal(
        AgreementTest.outcome(reference.parse(slow)(source)),
        AgreementTest.outcome(strict.parse(fast)(source)),
      ) && outcomes.equal(
        AgreementTest.outcome(reference.parseAll(slow)(source)),
        AgreementTest.outcome(strict.parseAll(fast)(source)),
      )
    }
  }
  test("a rule of a family may begin with a call of another rule, on both interpreters") {
    for semantics <- List[Semantics](reference.Semantics, strict.Semantics) do {
      val expression = Arithmetic(semantics.algebra).expression

      val _ = assert(semantics.run(expression)((), "1+2*3") == Some((7, 5)))
      val _ = assert(semantics.run(expression)((), "(1+2)*3") == Some((9, 7)))
      assert(semantics.run(expression)((), "2*(3+4)*5+1") == Some((71, 11)))
    }
  }

  test("a recursive call after a lookahead is unguarded and fails, on both interpreters") {
    for semantics <- List[Semantics](reference.Semantics, strict.Semantics) do {
      val rule = LookaheadRecursion(semantics.algebra).rule

      assert(AgreementTest.returned(semantics)(rule, "a") == Some(Some(("a", 1))))
    }
  }
}

object AgreementTest {

  /** What `p` returns on `source`, or nothing if it overflows the stack. */
  def returned[B](semantics: Semantics)(p: semantics.algebra.P[Unit, B], source: String): Option[Option[(B, Int)]] = {
    try Some(semantics.run(p)((), source))
    catch { case _: StackOverflowError => None }
  }

  /** The parser denoted by `term` in `alg`, at the semantic input `n`. */
  def closed(alg: ParserAlgebra)(term: Term, n: Int): alg.P[Unit, Int] = {
    import alg.*
    Grammars.interpret(alg)(term).mapInput(lift((_: Unit) => n))
  }

  /** Whether the parser denoted by `term` returns at `in`, without overflowing the stack. */
  def total(semantics: Semantics)(term: Term, in: ReferenceParser.Input, n: Int): Boolean = {
    try {
      val _ = semantics.diagnose(Grammars.interpret(semantics.algebra)(term))(n, in.source, in.offset)
      true
    } catch { case _: StackOverflowError => false }
  }

  /** What a parse returns, as comparable data: the message of its error, or its result and offset. */
  def outcome(parsed: scala.util.Try[(result: Int, offset: Int)]): Either[String, (Int, Int)] = {
    parsed.fold(error => Left(error.getMessage.nn), success => Right((success.result, success.offset)))
  }
}
