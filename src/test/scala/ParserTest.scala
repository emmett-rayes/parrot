package parrot

import org.scalatest.funsuite.AnyFunSuite

import scala.util.Success

class ParserTest extends AnyFunSuite {
  import Kleisli.given
  import Parser.{run, given}
  import StateT.given

  private val P    = ParserAlgebra[Parser]
  private val Prof = Profunctor[Parser]
  import Prof.rmap

  test("a literal consumes a matching prefix") {
    val parser = P.literal("hello")
    assert(parser.run("hello world") == Success((result = "hello", state = " world")))
  }

  test("a literal fails on a mismatch") {
    val parser = P.literal("hello")
    assert(parser.run("goodbye").isFailure)
  }

  test("a literal consuming the whole input leaves an empty remainder") {
    val parser = P.literal("hello")
    assert(parser.run("hello") == Success((result = "hello", state = "")))
  }

  test("the empty literal succeeds without consuming input") {
    val parser = P.literal("")
    assert(parser.run("hello") == Success((result = "", state = "hello")))
  }

  test("success succeeds with the given result without consuming input") {
    val expected = 42
    val parser   = P.success[Unit, Int](expected)
    assert(parser.run("hello") == Success((result = expected, state = "hello")))
  }

  test("success ignores the semantic input") {
    val expected = 42
    val parser   = P.success[String, Int](expected)
    assert(parser.run("ignored", "hello") == Success((result = expected, state = "hello")))
  }

  test("success succeeds on empty input") {
    val parser = P.success[Unit, String]("result")
    assert(parser.run("") == Success((result = "result", state = "")))
  }

  test("failure fails without consuming input") {
    val parser = P.failure[Unit, Int]
    assert(parser.run("hello").isFailure)
  }

  test("failure ignores the semantic input") {
    val parser = P.failure[String, Int]
    assert(parser.run("ignored", "hello").isFailure)
  }

  test("failure fails on empty input") {
    val parser = P.failure[Unit, String]
    assert(parser.run("").isFailure)
  }

  test("lookahead succeeds without consuming input if the underlying parser succeeds") {
    val parser = ~P.literal("hello")
    assert(parser.run("hello world") == Success((result = (), state = "hello world")))
  }

  test("lookahead fails if the underlying parser fails") {
    val parser = ~P.literal("hello")
    assert(parser.run("goodbye").isFailure)
  }

  test("lookahead followed by the parser consumes the input normally (bar(p) >> p == p)") {
    val p      = P.literal("hello")
    val parser = ~p >> p
    assert(parser.run("hello world") == Success((result = "hello", state = " world")))
  }

  test("not succeeds without consuming input if the underlying parser fails") {
    val parser = !P.literal("hello")
    assert(parser.run("goodbye") == Success((result = (), state = "goodbye")))
  }

  test("not fails if the underlying parser succeeds") {
    val parser = !P.literal("hello")
    assert(parser.run("hello world").isFailure)
  }

  test("not guards subsequent parser execution when the prefix does not match") {
    val parser = !P.literal("hello") >> P.literal("world")
    assert(parser.run("world") == Success((result = "world", state = "")))
  }

  test("not blocks subsequent parser execution when the prefix matches") {
    val parser = !P.literal("hello") >> P.literal("world")
    assert(parser.run("hello world").isFailure)
  }

  test("andThen sequences two successful parsers") {
    val p1     = P.literal("hello")
    val p2     = P.success[String, Int](42)
    val parser = p1 >> p2
    assert(parser.run("hello world") == Success((result = 42, state = " world")))
  }

  test("andThen chains parsers consuming subsequent input") {
    val p1     = P.literal("hello")
    val bridge = P.success[String, Unit](())
    val p2     = P.literal(" world")
    val parser = p1 >> bridge >> p2
    assert(parser.run("hello world!") == Success((result = " world", state = "!")))
  }

  test("andThen fails if the first parser fails") {
    val p1     = P.literal("hello")
    val p2     = P.success[String, Int](42)
    val parser = p1 >> p2
    assert(parser.run("goodbye").isFailure)
  }

  test("andThen fails if the second parser fails") {
    val p1     = P.literal("hello")
    val p2     = P.failure[String, Int]
    val parser = p1 >> p2
    assert(parser.run("hello world").isFailure)
  }

  test("orElse succeeds with the first parser if it succeeds") {
    val p1     = P.literal("hello")
    val p2     = P.literal("world")
    val parser = p1 +> p2
    assert(parser.run("hello world") == Success((result = "hello", state = " world")))
  }

  test("orElse falls back to the second parser if the first parser fails") {
    val p1     = P.literal("hello")
    val p2     = P.literal("world")
    val parser = p1 +> p2
    assert(parser.run("world hello") == Success((result = "world", state = " hello")))
  }

  test("orElse fails if both parsers fail") {
    val p1     = P.literal("hello")
    val p2     = P.literal("world")
    val parser = p1 +> p2
    assert(parser.run("goodbye").isFailure)
  }

  test("either dispatches to the first parser yielding Left") {
    val p1     = P.literal("hello")
    val p2     = P.success[Unit, Int](42)
    val parser = p1 |> p2
    assert(parser.run("hello world") == Success((result = Left("hello"), state = " world")))
  }

  test("either falls back to the second parser yielding Right if the first fails") {
    val p1     = P.literal("hello")
    val p2     = P.success[Unit, Int](42)
    val parser = p1 |> p2
    assert(parser.run("world hello") == Success((result = Right(42), state = "world hello")))
  }

  test("either fails if both parsers fail") {
    val p1     = P.literal("hello")
    val p2     = P.literal("world")
    val parser = p1 |> p2
    assert(parser.run("goodbye").isFailure)
  }

  test("zip sequences two successful parsers pairing results") {
    val p1     = P.literal("hello")
    val p2     = P.literal(" world")
    val parser = p1 ** p2
    assert(parser.run(((), ()), "hello world!") == Success((result = ("hello", " world"), state = "!")))
  }

  test("zip passes semantic inputs to respective parsers") {
    val p1     = P.success[Int, String]("first")
    val p2     = P.success[Double, Boolean](true)
    val parser = p1 ** p2
    assert(parser.run((1, 2.0), "input") == Success((result = ("first", true), state = "input")))
  }

  test("zip fails if the first parser fails") {
    val p1     = P.failure[Unit, String]
    val p2     = P.literal(" world")
    val parser = p1 ** p2
    assert(parser.run(((), ()), "hello world").isFailure)
  }

  test("zip fails if the second parser fails") {
    val p1     = P.literal("hello")
    val p2     = P.failure[Unit, String]
    val parser = p1 ** p2
    assert(parser.run(((), ()), "hello world").isFailure)
  }

  test("branch dispatches to the first parser on Left input") {
    val p1     = P.literal("hello")
    val p2     = P.success[Unit, Int](42)
    val parser = p1 ++ p2
    assert(parser.run(Left(()), "hello world") == Success((result = Left("hello"), state = " world")))
  }

  test("branch dispatches to the second parser on Right input") {
    val p1     = P.literal("hello")
    val p2     = P.success[Unit, Int](42)
    val parser = p1 ++ p2
    assert(parser.run(Right(()), "hello world") == Success((result = Right(42), state = "hello world")))
  }

  test("branch fails if the first branch fails on Left input") {
    val p1     = P.literal("hello")
    val p2     = P.literal("world")
    val parser = p1 ++ p2
    assert(parser.run(Left(()), "goodbye").isFailure)
  }

  test("branch fails if the second branch fails on Right input") {
    val p1     = P.literal("hello")
    val p2     = P.literal("world")
    val parser = p1 ++ p2
    assert(parser.run(Right(()), "goodbye").isFailure)
  }

  test("merge dispatches to the first parser on Left input") {
    val p1     = P.literal("0x") >> P.success[String, Int](16)
    val p2     = P.success[Unit, Int](10)
    val parser = p1 || p2
    assert(parser.run(Left(()), "0xabc") == Success((result = 16, state = "abc")))
  }

  test("merge dispatches to the second parser on Right input") {
    val p1     = P.literal("0x") >> P.success[String, Int](16)
    val p2     = P.success[Unit, Int](10)
    val parser = p1 || p2
    assert(parser.run(Right(()), "abc") == Success((result = 10, state = "abc")))
  }

  test("merge fails if the first branch fails on Left input") {
    val p1     = P.literal("hello") >> P.success[String, Int](1)
    val p2     = P.literal("world") >> P.success[String, Int](2)
    val parser = p1 || p2
    assert(parser.run(Left(()), "goodbye").isFailure)
  }

  test("merge fails if the second branch fails on Right input") {
    val p1     = P.literal("hello") >> P.success[String, Int](1)
    val p2     = P.literal("world") >> P.success[String, Int](2)
    val parser = p1 || p2
    assert(parser.run(Right(()), "goodbye").isFailure)
  }

  test("loop terminates immediately when the step returns Left") {
    val step   = P.literal("hello").rmap(s => Left[String, Unit](s))
    val parser = step.loop
    assert(parser.run("hello world") == Success((result = "hello", state = " world")))
  }

  test("loop consumes tokens iteratively until termination") {
    val step: Parser[Int, Either[Int, Int]] =
      (n: Int) =>
        input =>
          if input.startsWith("x") then Success((Right(n + 1), input.drop(1)))
          else Success((Left(n), input))
    val parser = step.loop
    assert(parser.run(0, "xxxrest") == Success((result = 3, state = "rest")))
  }

  test("repeated consumes multiple consecutive matches") {
    val parser = P.literal("hello").repeated
    assert(parser.run("hellohello world") == Success((result = List("hello", "hello"), state = " world")))
  }

  test("repeated consumes a single match") {
    val parser = P.literal("hello").repeated
    assert(parser.run("hello world") == Success((result = List("hello"), state = " world")))
  }

  test("repeated succeeds with an empty list on a mismatch") {
    val parser = P.literal("hello").repeated
    assert(parser.run("goodbye") == Success((result = List.empty, state = "goodbye")))
  }

  test("repeated consuming the whole input leaves an empty remainder") {
    val parser = P.literal("hello").repeated
    assert(parser.run("hellohello") == Success((result = List("hello", "hello"), state = "")))
  }

  test("repeated succeeds on empty input") {
    val parser = P.literal("hello").repeated
    assert(parser.run("") == Success((result = List.empty, state = "")))
  }

  test("recursive supports direct left recursion and grows the seed") {
    val expr: Parser[Unit, String] = P.recursive[Unit, String] { rec =>
      val step: Parser[Unit, String] = (rec ** P.literal("+") ** P.literal("1")).dimap(
        (_: Unit) => (((), ()), ()),
        { case ((e, _), one) => s"($e+$one)" }
      )
      step +> P.literal("1")
    }

    assert(
      expr.run("1") == Success((result = "1", state = "")) &&
        expr.run("1+1") == Success((result = "(1+1)", state = "")) &&
        expr.run("1+1+1") == Success((result = "((1+1)+1)", state = "")) &&
        expr.run("1+1+1+1") == Success((result = "(((1+1)+1)+1)", state = "")) &&
        expr.run("x").isFailure,
    )
  }

  test("recursive supports non-left recursion") {
    val parens: Parser[Unit, String] = P.recursive[Unit, String] { rec =>
      val nested: Parser[Unit, String] = (P.literal("(") ** rec ** P.literal(")")).dimap(
        (_: Unit) => (((), ()), ()),
        { case ((_, inner), _) => s"[$inner]" }
      )
      nested +> P.literal("x")
    }

    assert(
      parens.run("x") == Success((result = "x", state = "")) &&
        parens.run("(x)") == Success((result = "[x]", state = "")) &&
        parens.run("((x))") == Success((result = "[[x]]", state = "")),
    )
  }

  test("recursive supports semantic input (e.g. left-associative accumulator)") {
    // A step parser that takes an accumulator acc: Int, parses "+1", and yields acc + 1
    val plusOne: Parser[Unit, Unit] = (P.literal("+") >> P.success[String, Unit](()) >> P.literal("1")).dimap(
      identity,
      _ => ()
    )
    val step: Parser[Int, Int] = (P.pure((acc: Int) => acc) ** plusOne).dimap(
      acc => (acc, ()),
      { case (acc, _) => acc + 1 }
    )

    // Left-recursive accumulator fold: rec >> step | pure(acc => acc)
    val fold: Parser[Int, Int] = P.recursive[Int, Int] { rec =>
      (rec >> step) +> P.pure(identity[Int])
    }

    assert(
      fold.run(0, "") == Success((result = 0, state = "")) &&
        fold.run(10, "+1") == Success((result = 11, state = "")) &&
        fold.run(10, "+1+1+1") == Success((result = 13, state = "")) &&
        fold.run(0, "+1+1+1+1") == Success((result = 4, state = "")),
    )
  }

  test("recursive supports a pair of mutually left-recursive parsers") {
    // E -> T '+' '1' | '1'
    // T -> E '*' '2' | '2'
    val (expr, term) = P.recursive[(Parser[Unit, String], Parser[Unit, String])] { (recE, recT) =>
      val eStep: Parser[Unit, String] = (recT ** P.literal("+") ** P.literal("1")).dimap(
        (_: Unit) => (((), ()), ()),
        { case ((t, _), one) => s"($t+$one)" }
      )
      val eRule = eStep +> P.literal("1")

      val tStep: Parser[Unit, String] = (recE ** P.literal("*") ** P.literal("2")).dimap(
        (_: Unit) => (((), ()), ()),
        { case ((e, _), two) => s"($e*$two)" }
      )
      val tRule = tStep +> P.literal("2")

      (eRule, tRule)
    }

    assert(
      expr.run("1") == Success((result = "1", state = "")) &&
        term.run("2") == Success((result = "2", state = "")) &&
        term.run("1*2") == Success((result = "(1*2)", state = "")) &&
        expr.run("2+1") == Success((result = "(2+1)", state = "")) &&
        expr.run("1*2+1") == Success((result = "((1*2)+1)", state = "")) &&
        term.run("1*2+1*2") == Success((result = "(((1*2)+1)*2)", state = "")),
    )
  }

  test("recursive supports an arbitrary N-tuple (e.g. 3) of mutually left-recursive parsers") {
    // E -> T '+' '1' | '1'
    // T -> F '*' '2' | '2'
    // F -> E '/' '3' | '3'
    type Rules = (Parser[Unit, String], Parser[Unit, String], Parser[Unit, String])

    val (expr, term, fact) = P.recursive[Rules] { (recE, recT, recF) =>
      val eStep: Parser[Unit, String] = (recT ** P.literal("+") ** P.literal("1")).dimap(
        (_: Unit) => (((), ()), ()),
        { case ((t, _), one) => s"($t+$one)" }
      )
      val eRule = eStep +> P.literal("1")

      val tStep: Parser[Unit, String] = (recF ** P.literal("*") ** P.literal("2")).dimap(
        (_: Unit) => (((), ()), ()),
        { case ((f, _), two) => s"($f*$two)" }
      )
      val tRule = tStep +> P.literal("2")

      val fStep: Parser[Unit, String] = (recE ** P.literal("/") ** P.literal("3")).dimap(
        (_: Unit) => (((), ()), ()),
        { case ((e, _), three) => s"($e/$three)" }
      )
      val fRule = fStep +> P.literal("3")

      (eRule, tRule, fRule)
    }

    assert(
      expr.run("1") == Success((result = "1", state = "")) &&
        term.run("2") == Success((result = "2", state = "")) &&
        fact.run("3") == Success((result = "3", state = "")) &&
        fact.run("1/3") == Success((result = "(1/3)", state = "")) &&
        term.run("3*2") == Success((result = "(3*2)", state = "")) &&
        expr.run("2+1") == Success((result = "(2+1)", state = "")) &&
        expr.run("3*2+1") == Success((result = "((3*2)+1)", state = "")) &&
        expr.run("1/3*2+1") == Success((result = "(((1/3)*2)+1)", state = "")) &&
        fact.run("3*2+1/3") == Success((result = "(((3*2)+1)/3)", state = "")) &&
        expr.run("1/3*2+1/3*2+1") == Success((result = "((((((1/3)*2)+1)/3)*2)+1)", state = "")),
    )
  }

  test("skipThen sequences two parsers keeping only the second result") {
    val p1     = P.literal("hello")
    val p2     = P.literal("world")
    val parser = p1.skipThen(p2)
    assert(
      parser.run("helloworld") == Success((result = "world", state = "")) &&
        parser.run("hellogoodbye").isFailure,
    )
  }

  test("thenSkip sequences two parsers keeping only the first result") {
    val p1     = P.literal("hello")
    val p2     = P.literal("world")
    val parser = p1.thenSkip(p2)
    assert(
      parser.run("helloworld") == Success((result = "hello", state = "")) &&
        parser.run("hellogoodbye").isFailure,
    )
  }

  test("between sequences first, self, and second, keeping only the result of self") {
    val p = P.literal("content").between(P.literal("("), P.literal(")"))
    assert(
      p.run("(content)") == Success((result = "content", state = "")) &&
        p.run("(content").isFailure,
    )
  }

  test("optional succeeds with Some when self succeeds and None when self fails") {
    val p = P.literal("hello").optional
    assert(
      p.run("hello world") == Success((result = Some("hello"), state = " world")) &&
        p.run("goodbye") == Success((result = None, state = "goodbye")),
    )
  }

  test("separatedBy matches elements separated by a delimiter") {
    val p = P.literal("a").separatedBy(P.literal(","))
    assert(
      p.run("a,a,arest") == Success((result = List("a", "a", "a"), state = "rest")) &&
        p.run("a") == Success((result = List("a"), state = "")) &&
        p.run("b").isFailure,
    )
  }

  test("times matches a parser exactly n times") {
    val p = P.literal("x").times(3)
    assert(
      p.run("xxxrest") == Success((result = List("x", "x", "x"), state = "rest")) &&
        p.run("xx").isFailure &&
        P.literal("x").times(0).run("rest") == Success((result = List.empty, state = "rest")),
    )
  }

  test("atLeast matches a parser at least n times") {
    val p = P.literal("x").atLeast(2)
    assert(
      p.run("xxxxrest") == Success((result = List("x", "x", "x", "x"), state = "rest")) &&
        p.run("xxrest") == Success((result = List("x", "x"), state = "rest")) &&
        p.run("xrest").isFailure &&
        p.run("").isFailure &&
        P.literal("x").atLeast(0).run("rest") == Success((result = List.empty, state = "rest")),
    )
  }

  test("pair sequences two parsers pairing both results") {
    val p = P.literal("a") && P.literal("b")
    assert(p.run("ab") == Success((result = ("a", "b"), state = "")))
  }

  test("union returns the union of results") {
    val p1: Parser[Unit, Int]    = P.literal("1").rmap(_ => 1)
    val p2: Parser[Unit, String] = P.literal("two")
    val unionParser              = p1.union(p2)
    assert(
      unionParser.run("1") == Success((result = 1, state = "")) &&
        unionParser.run("two") == Success((result = "two", state = "")),
    )
  }
}
