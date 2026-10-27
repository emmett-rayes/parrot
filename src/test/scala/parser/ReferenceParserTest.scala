package parrot
package parser

import org.scalatest.funsuite.AnyFunSuite

/** Behavior of [[ReferenceParser]]: the specification, on examples. */
class ReferenceParserTest extends AnyFunSuite {
  private val parser = ReferenceParser()
  import parser.*

  given CanEqual[Any, Any] = CanEqual.derived

  private val a      = literal("a")
  private val b      = literal("b")
  private val as     = regex("a+".r)
  private val digits = regex("[0-9]+".r)

  test("literal and regex consume a prefix") {
    val _ = assert(a.parse("ab").get == (result = "a", offset = 1))
    val _ = assert(as.parse("aab").get == (result = "aa", offset = 2))
    val _ = assert(digits.parse("123abc").get == (result = "123", offset = 3))
    assert(b.parse("ab").isFailure)
  }

  test("sequencing and skipThen / thenSkip") {
    val _ = assert((a *> b).parse("ab").get == (result = "b", offset = 2))
    val _ = assert((a <* b).parse("ab").get == (result = "a", offset = 2))
    assert(as.between(literal("("), literal(")")).parse("(aa)").get == (result = "aa", offset = 4))
  }

  test("pairing and map") {
    val _ = assert((a && b).map((x, y) => s"$x+$y").parse("ab").get == (result = "a+b", offset = 2))
    assert((a && b).parse("ab").get == (result = ("a", "b"), offset = 2))
  }

  test("ordered choice, attempt and merge") {
    val either = a |> b
    val _      = assert(either.parse("a").get == (result = "a", offset = 1))
    val _      = assert(either.parse("b").get == (result = "b", offset = 1))
    val _      = assert(either.parse("c").isFailure)
    val _      = assert((a +> b).parse("b").get == (result = Right("b"), offset = 1))
    val _      = assert(a.attempt.parse("b").get == (result = Right(()), offset = 0))
    assert(((a +> b) >> (pure[String, Int](_.length) || pure(_ => 0))).parse("a").get == (result = 1, offset = 1))
  }

  test("lookahead and not consume nothing") {
    val _ = assert((~a).parse("ab").get == (result = (), offset = 0))
    val _ = assert((!b).parse("ab").get == (result = (), offset = 0))
    val _ = assert((!a).parse("ab").isFailure)
    val _ = assert((~a *> a).parse("ab").get == (result = "a", offset = 1))
    val _ = assert((!b *> a).parse("ab").get == (result = "a", offset = 1))
    assert((!a *> a).parse("ab").isFailure)
  }

  test("repeated, times, atLeast and separatedBy") {
    val _ = assert(a.repeated.parse("aaab").get == (result = Vector("a", "a", "a"), offset = 3))
    val _ = assert(a.repeated.parse("b").get == (result = Vector.empty, offset = 0))
    val _ = assert(a.times(2).parse("aaa").get == (result = Vector("a", "a"), offset = 2))
    val _ = assert(a.times(2).parse("ab").isFailure)
    val _ = assert(a.atLeast(2).parse("aaab").get == (result = Vector("a", "a", "a"), offset = 3))
    val _ = assert(a.atLeast(2).parse("ab").isFailure)
    assert(a.separatedBy(literal(",")).parse("a,a,ab").get == (result = Vector("a", "a", "a"), offset = 5))
  }

  test("repetition is guarded: an item that succeeds without consuming input fails the repetition") {
    val _ = assert(literal("").repeated.parse("a").isFailure)
    val _ = assert(regex("b*".r).repeated.parse("bba").isFailure)
    assert(regex("b*".r).times(3).parse("bba").get == (result = Vector("bb", "", ""), offset = 2))
  }

  test("iteration is guarded: a step that continues without consuming input fails the loop") {
    val step: P[Int, Either[Int, Int]] = pure(n => if n > 0 then Right(n - 1) else Left(n))
    val _                              = assert(parser.run(step.iterate)(0, "").contains((0, 0)))
    assert(parser.run(step.iterate)(3, "").isEmpty)
  }

  test("recursive parsing") {
    val nested: P[Unit, String] = recursive[Unit, String](self => literal("(") *> self <* literal(")") |> literal("x"))
    val _                       = assert(nested.parseAll("((x))").get == (result = "x", offset = 5))
    assert(nested.parseAll("((x)").isFailure)
  }

  test("recursion is guarded: a left-recursive call fails, so only the other alternatives remain") {
    val expr =
      recursive[Unit, String](self => (self <* literal("+") && literal("1")).map((e, o) => s"($e+$o)") |> literal("1"))
    assert(expr.parse("1+1").get == (result = "1", offset = 1))
  }

  test("recursive solves mutual recursion, and accepts only tuples of parsers") {
    val (even, odd) = recursive[(P[Unit, Int], P[Unit, Int])] { rules =>
      ((a *> rules._2).map(_ + 1) |> pure(_ => 0), (a *> rules._1).map(_ + 1))
    }
    val _ = assert(even.parseAll("aaaa").get == (result = 4, offset = 4))
    val _ = assert(odd.parseAll("aaa").get == (result = 3, offset = 3))
    val _ = assert(even.parseAll("aaa").isFailure)
    assertDoesNotCompile("recursive[(Int, String)](t => t)")
  }

  test("parseAll requires the end of input") {
    val _ = assert(a.parseAll("a").get == (result = "a", offset = 1))
    assert(a.parseAll("ab").isFailure)
  }
}

/** Diagnostics of [[ReferenceParser]]: the furthest failure, with rule names as context. */
class DiagnosticsTest extends AnyFunSuite {
  private val parser = ReferenceParser()
  import parser.*

  given CanEqual[Any, Any] = CanEqual.derived

  private def expected(position: Int, labels: (String, List[String])*): Expected = {
    Expected(position, labels.map((label, context) => Expectation(label, context)).toSet)
  }

  test("the furthest failure wins; failures at the same position are joined") {
    val p = (literal("a") *> literal("b")) |> literal("c")
    val _ = assert(diagnose(p)((), "ax")._1 == expected(1, ("\"b\"", Nil)))
    assert(diagnose(p)((), "x")._1 == expected(0, ("\"a\"", Nil), ("\"c\"", Nil)))
  }

  test("a successful parse also reports what it expected: a repetition stops where its item fails") {
    val p = literal("a").repeated
    assert(diagnose(p)((), "aab") == (expected(2, ("\"a\"", Nil)), Some((Vector("a", "a"), 2))))
  }

  test("lookahead and negation are silent") {
    val _ = assert(diagnose(~literal("a"))((), "b")._1 == Expected.bottom)
    assert(diagnose(!literal("b") *> literal("c"))((), "a")._1 == expected(0, ("\"c\"", Nil)))
  }

  test("a rule that fails at its start reports its own name; otherwise it adds itself to the context") {
    val digit  = regex("[0-9]".r).rule("digit")
    val number = (digit && digit.repeated).rule("number")
    val _      = assert(diagnose(number)((), "x")._1 == expected(0, ("number", Nil)))
    assert(diagnose(number)((), "1x")._1 == expected(1, ("digit", List("number"))))
  }

  test("parse errors render the expectations in a deterministic order") {
    val p = (literal("b") |> literal("a")).rule("letter")
    val _ = assert(p.parse("x").failed.get.getMessage == "expected letter at position 0")
    assert((literal("b") |> literal("a")).parse("x").failed.get.getMessage == "expected \"a\" or \"b\" at position 0")
  }

  test("parseAll joins the end of input with what the parse expected") {
    val p = literal("a").repeated
    assert(p.parseAll("aab").failed.get.getMessage == "expected \"a\" or end of input at position 2")
  }

  test("a parse that fails without expecting anything is reported at the start") {
    val _ = assert(failure[Unit, Unit].parse("x").failed.get.getMessage == "no parse at position 0")
    val _ = assert(ParseError(Expected.bottom).offset == 0)
    assert((!literal("a")).parse("a").failed.get.getMessage == "no parse at position 0")
  }

  test("regular expressions are matched in context") {
    val _ = assert(regex("^a".r).parse("ab").isSuccess)
    val _ = assert((literal("a") *> regex("^b".r)).parse("ab").isFailure)
    val _ = assert((literal("a") *> regex("(?<=a)b".r)).parse("ab").isSuccess)
    val _ = assert((literal("a") *> regex("\\b".r)).parse("a b").get.offset == 1)
    val _ = assert(regex("b$".r).parse("bc").isFailure)
    assert(regex("[^x]".r).parse("\uD83D\uDE00").get.offset == 2)
  }

  test("ordered choice runs its second alternative only where the first fails") {
    val nested = (1 to 40).foldLeft(literal("a"))((p, _) => p |> p)
    assert(nested.parse("a").get.offset == 1)
  }
}
