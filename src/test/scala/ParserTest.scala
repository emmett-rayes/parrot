package parrot

import org.scalatest.funsuite.AnyFunSuite

import scala.util.Success

class ParserTest extends AnyFunSuite {
  import Parser.{run, given}

  private val P = ParserAlgebra[Parser]

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
}
