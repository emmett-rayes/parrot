package parrot
package parser

import org.scalatest.funsuite.AnyFunSuite

import scala.util.{Failure as TryFailure, Success as TrySuccess, Try}

/** Behavior of [[StrictParser]]: normal forms, dispatch, left recursion and agreement on named grammars. */
class StrictParserTest extends AnyFunSuite {
  import StrictParserTest.*
  import parser.{Choice as _, *}
  import StrictParser.Node.*

  given CanEqual[Any, Any] = CanEqual.derived

  /** The result of a parse. Computed outside `assert`: a lambda inside ScalaTest's `assert` macro defeats capture
    * checking.
    */
  private def result[B](parsed: Try[(result: B, offset: Int)]): Try[B] = parsed.map(_.result)

  /** The offset after a parse, computed outside `assert`. */
  private def offset[B](parsed: Try[(result: B, offset: Int)]): Try[Int] = parsed.map(_.offset)

  private val a = literal("a")
  private val b = literal("b")
  private val c = literal("c")

  test("the derived concatenation combinators normalize to dedicated nodes") {
    val _ = assert((a && b) == Pair(Literal("a"), Literal("b")))
    val _ = assert((a *> b) == SkipThen(Literal("a"), Literal("b")))
    val _ = assert((a <* b) == ThenSkip(Literal("a"), Literal("b")))
    assert(b.between(a, c) == ThenSkip(SkipThen(Literal("a"), Literal("b")), Literal("c")))
  }

  test("branching and merging normalize to Merge, zipping with success to Zip") {
    val _ = assert((a || b) == Merge(Literal("a"), Literal("b")))
    val _ = assert((a ++ b) == Merge(Seq(Literal("a"), Pure(Fn.Inl())), Seq(Literal("b"), Pure(Fn.Inr()))))
    assert((a ** success[Int]) == Zip(Literal("a"), Success()))
  }

  test("identities are eliminated and pure functions fused") {
    val f = lift((s: String) => s.length)
    val _ = assert((success[Unit] >> a >> success[String]) == Literal("a"))
    val _ = assert(pure(Fn.id[Int]) == Success[Int]())
    val _ = assert(a.map(Fn.id[String]) == Literal("a"))
    val _ = assert(a.map(f).map(lift((n: Int) => n + 1)).isInstanceOf[Seq[?, ?, ?]])
    assert((a && a).map(Fns.Product.fst).map(f) == Seq(ThenSkip(Literal("a"), Literal("a")), Pure(f)))
  }

  test("choices are flattened and pure functions distributed over them") {
    val f = lift((s: String) => s.length)
    val g = lift((s: String) => -s.length)
    val _ = assert((a |> b |> c) == Choice(List(Literal("a"), Literal("b"), Literal("c"))))
    val _ = assert((a |> (b |> c)) == Choice(List(Literal("a"), Literal("b"), Literal("c"))))
    val _ = assert((a |> failure) == Literal("a"))
    val _ = assert((a |> b).map(f) == Choice(List(Seq(Literal("a"), Pure(f)), Seq(Literal("b"), Pure(f)))))
    val _ =
      assert((a +> b).map(Fn.copair(f, g)) == Choice(List(Seq(Literal("a"), Pure(f)), Seq(Literal("b"), Pure(g)))))
    assert(a.attempt == Choice(List(Seq(Literal("a"), Pure(Fn.Inl())), Pure(Fn.Inr()))))
  }

  test("character-class regexes compile to scanners") {
    val _ = assert(regex("[0-9]+".r).isInstanceOf[Scan])
    val _ = assert(regex("[1-9][0-9]*".r).isInstanceOf[Scan])
    val _ = assert(regex("[^\"\\\\\\u0000-\\u001f]+".r).isInstanceOf[Scan])
    val _ = assert(regex("a*a".r).isInstanceOf[Pattern])
    assert(regex("(ab)+".r).isInstanceOf[Pattern])
  }

  test("choices dispatch on the next character, and report every alternative that failed") {
    val keyword = literal("true") |> literal("false") |> literal("null") |> regex("[0-9]+".r)
    val _       = assert(result(keyword.parse("null")) == TrySuccess("null"))
    val _       = assert(result(keyword.parse("42")) == TrySuccess("42"))
    val all     = Set("\"true\"", "\"false\"", "\"null\"", "/[0-9]+/").map(Expectation(_, Nil))
    val _       = assert(keyword.parse("x") == TryFailure(ParseError(Expected(0, all))))
    val _       = assert(keyword.parse("") == TryFailure(ParseError(Expected(0, all))))
    assert(offset((literal("") |> literal("a")).parse("a")) == TrySuccess(0))
  }

  test("dispatch accounts for what nullable repetitions and patterns may consume") {
    val repeat  = a.separatedBy(b).map(lift(_.size)) |> pure(lift(_ => -1))
    val pattern = (regex("a*a".r) *> c).map(lift(_.length)) |> pure(lift(_ => -1))
    val _       = assert(result(repeat.parse("abac")) == TrySuccess(2))
    assert(result(pattern.parse("aac")) == TrySuccess(1))
  }

  test("left recursion grows the seed (an extension beyond the reference)") {
    val expr = recursive[Unit, String](rec =>
      (rec <* literal("+") && literal("1")).map(lift((e, one) => s"($e+$one)")) |> literal("1")
    )
    val _ = assert(result(expr.parse("1")) == TrySuccess("1"))
    val _ = assert(result(expr.parse("1+1")) == TrySuccess("(1+1)"))
    val _ = assert(result(expr.parse("1+1+1")) == TrySuccess("((1+1)+1)"))
    val _ = assert(result(expr.parseAll("1+1+1+1")) == TrySuccess("(((1+1)+1)+1)"))
    assert(expr.parse("x").isFailure)
  }

  test("non-left recursion") {
    val parens = recursive[Unit, String](rec =>
      rec.between(literal("("), literal(")")).map(lift(inner => s"[$inner]")) |> literal("x")
    )
    val _ = assert(result(parens.parseAll("x")) == TrySuccess("x"))
    val _ = assert(result(parens.parseAll("(x)")) == TrySuccess("[x]"))
    assert(result(parens.parseAll("((x))")) == TrySuccess("[[x]]"))
  }

  test("left recursion with a semantic input: a left-associative accumulator") {
    val plusOne = (literal("+") *> literal("1")).mapInput(lift((_: Int) => ()))
    val step    = (plusOne *> success[Int]).map(lift(_ + 1))
    val fold    = recursive[Int, Int](rec => (rec >> step) |> success[Int])
    val _       = assert(parser.run(fold)(0, "").contains((0, 0)))
    val _       = assert(parser.run(fold)(10, "+1").contains((11, 2)))
    val _       = assert(parser.run(fold)(10, "+1+1+1").contains((13, 6)))
    assert(parser.run(fold)(0, "+1+1+1+1").contains((4, 8)))
  }

  test("a recursive call at the same position with another semantic input fails, as guarded recursion does") {
    val countdown = recursive[Int, Int](rec => (pure(lift((n: Int) => n - 1)) >> rec) |> success[Int])
    assert(parser.run(countdown)(3, "").contains((3, 0)))
  }

  test("a pair of mutually left-recursive parsers") {
    val (expr, term) = recursive[(P[Unit, String], P[Unit, String])] { (recE, recT) =>
      val e = (recT <* literal("+") && literal("1")).map(lift((t, one) => s"($t+$one)")) |> literal("1")
      val t = (recE <* literal("*") && literal("2")).map(lift((e, two) => s"($e*$two)")) |> literal("2")
      (e, t)
    }
    val _ = assert(result(expr.parseAll("1")) == TrySuccess("1"))
    val _ = assert(result(term.parseAll("2")) == TrySuccess("2"))
    val _ = assert(result(term.parseAll("1*2")) == TrySuccess("(1*2)"))
    val _ = assert(result(expr.parseAll("2+1")) == TrySuccess("(2+1)"))
    val _ = assert(result(expr.parseAll("1*2+1")) == TrySuccess("((1*2)+1)"))
    assert(result(term.parseAll("1*2+1*2")) == TrySuccess("(((1*2)+1)*2)"))
  }

  test("a triple of mutually left-recursive parsers") {
    def step(rec: P[Unit, String], op: String, operand: String): P[Unit, String] = {
      (rec <* literal(op) && literal(operand)).map(lift((l, r) => s"($l$op$r)")) |> literal(operand)
    }
    val (expr, term, fact) = recursive[(P[Unit, String], P[Unit, String], P[Unit, String])] { (recE, recT, recF) =>
      (step(recT, "+", "1"), step(recF, "*", "2"), step(recE, "/", "3"))
    }
    val _ = assert(result(expr.parseAll("1")) == TrySuccess("1"))
    val _ = assert(result(fact.parseAll("1/3")) == TrySuccess("(1/3)"))
    val _ = assert(result(term.parseAll("3*2")) == TrySuccess("(3*2)"))
    val _ = assert(result(expr.parseAll("3*2+1")) == TrySuccess("((3*2)+1)"))
    assert(result(expr.parseAll("1/3*2+1/3*2+1")) == TrySuccess("((((((1/3)*2)+1)/3)*2)+1)"))
  }

  private val reference = ReferenceParser()
  private val inputs    =
    List("", "a", "b", "ab", "aab", "aaab", "abab", "a,a,a", "a,a,", "(a)", "((a))", "((a)", "[1, 22]")

  private def agree[B](name: String)(grammar: Grammar[B]): Unit = {
    test(s"StrictParser agrees with ReferenceParser on $name") {
      val expected = grammar(reference)
      val actual   = grammar(parser)
      for input <- inputs do {
        val _ = assert(parser.run(actual)((), input) == reference.run(expected)((), input), s"on input \"$input\"")
      }
    }
  }

  agree("sequencing")(sequencingGrammar)
  agree("choice and lookahead")(choiceAndLookaheadGrammar)
  agree("repetition")(repetitionGrammar)
  agree("merge and loop")(mergeAndLoopGrammar)
  agree("recursion")(recursionGrammar)

  test("a parse that fails without expecting anything is reported at the start") {
    val _ = assert(failure[Unit, Unit].parse("x").failed.get.getMessage == "no parse at position 0")
    val _ = assert(ParseError(Expected.bottom).offset == 0)
    assert((!literal("a")).parse("a").failed.get.getMessage == "no parse at position 0")
  }

  test("regular expressions are matched in context, by the scanner and by the fallback alike") {
    val _ = assert(regex("^a".r).parse("ab").isSuccess)
    val _ = assert((literal("a") *> regex("^b".r)).parse("ab").isFailure)
    val _ = assert((literal("a") *> regex("(?<=a)b".r)).parse("ab").isSuccess)
    val _ = assert(offset((literal("a") *> regex("\\b".r)).parse("a b")) == TrySuccess(1))
    val _ = assert(regex("b$".r).parse("bc").isFailure)
    val _ = assert(regex("[^x]".r).isInstanceOf[Scan])
    assert(offset(regex("[^x]".r).parse("\uD83D\uDE00")) == TrySuccess(2))
  }
}

object StrictParserTest {
  val parser: StrictParser = StrictParser()

  /** A grammar written once against any algebra. */
  trait Grammar[B] {
    def apply(alg: ParserAlgebra): alg.P[Unit, B]
  }

  val sequencingGrammar: Grammar[(String, String)] = new Grammar[(String, String)] {
    def apply(alg: ParserAlgebra): alg.P[Unit, (String, String)] = {
      import alg.*
      (literal("a") *> literal("a")) && (literal("a") |> literal("b")).between(success[Unit], !literal("b"))
    }
  }

  val choiceAndLookaheadGrammar: Grammar[Either[Either[String, String], Unit]] =
    new Grammar[Either[Either[String, String], Unit]] {
      def apply(alg: ParserAlgebra): alg.P[Unit, Either[Either[String, String], Unit]] = {
        import alg.*
        ((literal("a") <* ~literal("b")) +> literal("b")).attempt
      }
    }

  val repetitionGrammar: Grammar[(Vector[String], (Vector[String], Vector[String]))] =
    new Grammar[(Vector[String], (Vector[String], Vector[String]))] {
      def apply(alg: ParserAlgebra): alg.P[Unit, (Vector[String], (Vector[String], Vector[String]))] = {
        import alg.*
        val a     = literal("a")
        val empty = lift[Unit, (Vector[String], (Vector[String], Vector[String]))](_ =>
          (Vector.empty, (Vector.empty, Vector.empty))
        )
        val list = a.separatedBy(literal(",")).attempt.map(lift(_.fold(v => v, _ => Vector.empty[String])))
        ~a.times(1) *> (a.atLeast(1) && (literal(",").repeated && list)) |> pure(empty)
      }
    }

  val mergeAndLoopGrammar: Grammar[Int] = new Grammar[Int] {
    def apply(alg: ParserAlgebra): alg.P[Unit, Int] = {
      import alg.*
      val step: P[Int, Either[Int, Int]] = (literal("a").mapInput(lift((_: Int) => ())) && success[Int]).map(lift(
        (_, n) => Right(n + 1)
      )) |>
        pure(lift(Left(_)))
      (literal("b") +> success[Unit]) >> (pure(lift((_: String) => 100)) || pure(lift(_ => 0))) >> step.iterate
    }
  }

  val recursionGrammar: Grammar[(Int, List[Int])] = new Grammar[(Int, List[Int])] {
    def apply(alg: ParserAlgebra): alg.P[Unit, (Int, List[Int])] = {
      import alg.*
      val nested = recursive[Unit, Int](self =>
        literal("a").map(lift(_ => 0)) |> self.between(literal("("), literal(")")).map(lift(_ + 1))
      )
      val number = regex("[0-9]+".r).map(lift(_.toInt))
      val list   = number.separatedBy(regex(", *".r)).between(literal("["), literal("]")).map(lift(_.toList))
      (nested +> list).map(lift(_.fold((_, Nil), (-1, _))))
    }
  }
}
