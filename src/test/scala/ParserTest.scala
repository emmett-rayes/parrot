package parrot

import org.scalatest.funsuite.AnyFunSuite

import scala.util.Success

class ParserTest extends AnyFunSuite {
  import Parser.run

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
}
