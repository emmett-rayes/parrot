package parrot
package parser

import category.*
import org.scalacheck.Gen

import Sample.given

/** The equations of parsing expression grammars, on random grammars, for an interpreter. */
abstract class ParserLawSpec(name: String, tracked val algebra: ParserAlgebra) extends LawSuite("PEG", name) {
  import algebra.*
  import algebra.ParserLaws.*

  private lazy val parsers: Gen[P[Int, Int]]                = Grammars.terms.map(Grammars.interpret(algebra))
  private lazy val observe: Gen[P[Int, Int] is Observable]  = ParserGen.exact[Int, Int](algebra)
  private lazy val semantic: Gen[P[Int, Int] is Observable] = ParserGen.observe[Int, Int](algebra)
  private lazy val order: Gen[P[Int, Int] is Preorder]      = ParserGen.order[Int, Int](algebra)

  /** A parser and one that reports at least as much: where *p* fails, it also runs *q* and fails. */
  private lazy val refined: Gen[(P[Int, Int], P[Int, Int])] = {
    Gen.zip(parsers, parsers).map((p, q) => (p, p |> (q >> failure[Int, Int])))
  }
  private lazy val steps: Gen[P[Int, Either[Int, Int]]]   = Grammars.terms.map(Grammars.step(algebra))
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
    forAll(ParserGen.exact[(Int, Int), (Int, Int)](algebra)) { o =>
      given (P[(Int, Int), (Int, Int)] is Observable) = o
      zipIdentity[Int, Int]
    }
  }

  law("zipDefinition") {
    forAll(ParserGen.exact[(Int, Int), (Int, Int)](algebra), parsers, parsers) { (o, p, q) =>
      given (P[(Int, Int), (Int, Int)] is Observable) = o
      zipDefinition(p, q)
    }
  }

  law("branchDefinition") {
    forAll(ParserGen.exact[Either[Int, Int], Either[Int, Int]](algebra), parsers, parsers) { (o, p, q) =>
      given (P[Either[Int, Int], Either[Int, Int]] is Observable) = o
      branchDefinition(p, q)
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
    forAll(ParserGen.exact[Int, Either[Int, Int]](algebra), parsers) { (o, p) =>
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
    forAll(ParserGen.exact[Int, Vector[Int]](algebra), consuming) { (o, p) =>
      given (P[Int, Vector[Int]] is Observable) = o
      repeatedUnfolding(p)
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
    forAll(ParserGen.order[(Int, Int), (Int, Int)](algebra), refined, refined) { case (o, (p, p2), (q, q2)) =>
      given (P[(Int, Int), (Int, Int)] is Preorder) = o
      zipMonotone(p, p2, q, q2)
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
}

class ReferenceParserLawTest extends ParserLawSpec("ReferenceParser", Interpreters.reference)

class StrictParserLawTest extends ParserLawSpec("StrictParser", Interpreters.strict)

/** The core invariant: on every grammar, the optimizing interpreter does what the reference does. */
class AgreementTest extends LawSuite("Agreement", "StrictParser") {
  import Interpreters.{reference, strict}

  law("results, offsets and diagnostics of ReferenceParser", "random grammars") {
    forAll(Grammars.terms, Grammars.sources, Gen.choose(-5, 5)) { (term, source, n) =>
      val expected = reference.diagnose(Grammars.interpret(reference)(term))(n, source)
      val actual   = strict.diagnose(Grammars.interpret(strict)(term))(n, source)
      Eq.Tuple2IsEq(using Expected.ExpectedIsEq, Eq.OptionIsEq(using Eq.Tuple2IsEq(using Eq.IntIsEq, Eq.IntIsEq)))
        .equal(expected, actual)
    }
  }

  law("results and offsets without diagnostics", "random grammars") {
    forAll(Grammars.terms, Grammars.sources, Gen.choose(-5, 5)) { (term, source, n) =>
      val expected = reference.run(Grammars.interpret(reference)(term))(n, source)
      val actual   = strict.run(Grammars.interpret(strict)(term))(n, source)
      Eq.OptionIsEq(using Eq.Tuple2IsEq(using Eq.IntIsEq, Eq.IntIsEq)).equal(expected, actual)
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
}

object AgreementTest {

  /** The parser denoted by `term` in `alg`, at the semantic input `n`. */
  def closed(alg: ParserAlgebra)(term: Term, n: Int): alg.P[Unit, Int] = {
    import alg.*
    Grammars.interpret(alg)(term).mapInput(lift((_: Unit) => n))
  }

  /** What a parse returns, as comparable data: the message of its error, or its result and offset. */
  def outcome(parsed: scala.util.Try[(result: Int, offset: Int)]): Either[String, (Int, Int)] = {
    parsed.fold(error => Left(error.getMessage.nn), success => Right((success.result, success.offset)))
  }
}
