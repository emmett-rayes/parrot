package parrot
package parser

import org.scalatest.funsuite.AnyFunSuite

class StrictParserTest extends AnyFunSuite {

  given CanEqual[Any, Any] = CanEqual.derived

  // =========================================================================
  // Construction-time normalization
  // =========================================================================

  test("StrictParser fuses the generic Pairing derivations into dedicated nodes") {
    import StrictParser.*
    import StrictParser.Node.*

    val a = literal("a")
    val b = literal("b")
    val c = literal("c")

    val _ = assert((a && b) == Pair(Literal("a"), Literal("b")))
    val _ = assert((a *> b) == SkipThen(Literal("a"), Literal("b")))
    val _ = assert((a <* b) == ThenSkip(Literal("a"), Literal("b")))
    val _ = assert(b.between(a, c) == ThenSkip(SkipThen(Literal("a"), Literal("b")), Literal("c")))
  }

  test("StrictParser fuses branching and zipping with success") {
    import StrictParser.*
    import StrictParser.Node.*

    val a = literal("a")
    val b = literal("b")

    val _ = assert((a || b) == Merge(Literal("a"), Literal("b")))
    val _ = assert(a.zip(success[Int]) == First(Literal("a")))
  }

  test("StrictParser eliminates identities and fuses pure morphisms") {
    import StrictParser.*
    import StrictParser.Node.*

    val a = literal("a")
    val f = Fn.lift((s: String) => s.length)

    val _ = assert((success[Unit] >> a >> success[String]) == Literal("a"))
    val _ = assert(pure(Fn.id[Int]) == Success[Int]())
    val _ = assert(a.map(Fn.id[String]) == Literal("a"))
    val _ = assert(a.map(f).map(Fn.lift((n: Int) => n + 1)).isInstanceOf[Seq[?, ?, ?]])
    val _ = assert((a && a).map(OnIsCartesian.first).map(f) == Seq(ThenSkip(Literal("a"), Literal("a")), Pure(f)))
  }

  test("StrictParser flattens choices and distributes pure functions over them") {
    import StrictParser.*
    import StrictParser.Node.*

    val a = literal("a")
    val b = literal("b")
    val c = literal("c")
    val f = Fn.lift((s: String) => s.length)
    val g = Fn.lift((s: String) => -s.length)

    val _ = assert((a |> b |> c) == Choice(List(Literal("a"), Literal("b"), Literal("c"))))
    val _ = assert((a |> (b |> c)) == Choice(List(Literal("a"), Literal("b"), Literal("c"))))
    val _ = assert((failure |> a |> success[Unit].map(Fn.lift(_ => "x")) |> b).isInstanceOf[Choice[?, ?]])
    val _ = assert((a |> failure) == Literal("a"))
    val _ = assert((a |> b).map(f) == Choice(List(Seq(Literal("a"), Pure(f)), Seq(Literal("b"), Pure(f)))))
    val _ =
      assert((a +> b).map(Fn.copair(f, g)) == Choice(List(Seq(Literal("a"), Pure(f)), Seq(Literal("b"), Pure(g)))))
  }

  test("StrictParser compiles character-class regexes to scanners") {
    import StrictParser.*
    import StrictParser.Node.*

    val _ = assert(regex("[0-9]+".r).isInstanceOf[Scan])
    val _ = assert(regex("[1-9][0-9]*".r).isInstanceOf[Scan])
    val _ = assert(regex("[^\"\\\\\\u0000-\\u001f]+".r).isInstanceOf[Scan])
    val _ = assert(regex("a*a".r).isInstanceOf[Pattern])
    val _ = assert(regex("(ab)+".r).isInstanceOf[Pattern])
  }

  test("StrictParser dispatches choices on the next character") {
    import StrictParser.*

    val keyword = literal("true") |> literal("false") |> literal("null") |> regex("[0-9]+".r)
    val _       = assert(keyword.parse("null").map(_.value) == Right("null"))
    val _       = assert(keyword.parse("42").map(_.value) == Right("42"))
    val _       = assert(keyword.parse("x") == Left((offset = 0, expected = "\"true\"")))
    val _       = assert(keyword.parse("") == Left((offset = 0, expected = "\"true\"")))
    val _       = assert((literal("") |> literal("a")).parse("a").map(_.offset) == Right(0))
  }

  // =========================================================================
  // Left recursion by seed growing (ported from the legacy interpreter)
  // =========================================================================

  test("recursive supports direct left recursion and grows the seed") {
    import StrictParser.*

    val expr = recursive[Unit, String] { rec =>
      (rec <* literal("+") && literal("1")).map(Fn.lift((e, one) => s"($e+$one)")) |> literal("1")
    }
    val _ = assert(expr.parse("1").map(_.value) == Right("1"))
    val _ = assert(expr.parse("1+1").map(_.value) == Right("(1+1)"))
    val _ = assert(expr.parse("1+1+1").map(_.value) == Right("((1+1)+1)"))
    val _ = assert(expr.parseAll("1+1+1+1").map(_.value) == Right("(((1+1)+1)+1)"))
    val _ = assert(expr.parse("x").isLeft)
  }

  test("recursive supports non-left recursion") {
    import StrictParser.*

    val parens = recursive[Unit, String] { rec =>
      rec.between(literal("("), literal(")")).map(Fn.lift(inner => s"[$inner]")) |> literal("x")
    }
    val _ = assert(parens.parseAll("x").map(_.value) == Right("x"))
    val _ = assert(parens.parseAll("(x)").map(_.value) == Right("[x]"))
    val _ = assert(parens.parseAll("((x))").map(_.value) == Right("[[x]]"))
  }

  test("recursive supports semantic input (e.g. a left-associative accumulator)") {
    import StrictParser.*

    val plusOne = (literal("+") *> literal("1")).mapInput(Fn.lift((_: Int) => ()))
    val step    = (plusOne *> success[Int]).map(Fn.lift(_ + 1))
    val fold    = recursive[Int, Int](rec => (rec >> step) |> success[Int])

    def run(acc: Int, input: String) = {
      val state = State(input)
      val out   = fold.run(acc, state)
      Option.when(!out.isFailed)((out.get, state.offset))
    }
    val _ = assert(run(0, "") == Some((0, 0)))
    val _ = assert(run(10, "+1") == Some((11, 2)))
    val _ = assert(run(10, "+1+1+1") == Some((13, 6)))
    val _ = assert(run(0, "+1+1+1+1") == Some((4, 8)))
  }

  test("recursive supports a pair of mutually left-recursive parsers") {
    import StrictParser.*

    // E -> T '+' '1' | '1'
    // T -> E '*' '2' | '2'
    val (expr, term) = recursive[(P[Unit, String], P[Unit, String])] { (recE, recT) =>
      val e = (recT <* literal("+") && literal("1")).map(Fn.lift((t, one) => s"($t+$one)")) |> literal("1")
      val t = (recE <* literal("*") && literal("2")).map(Fn.lift((e, two) => s"($e*$two)")) |> literal("2")
      (e, t)
    }
    val _ = assert(expr.parseAll("1").map(_.value) == Right("1"))
    val _ = assert(term.parseAll("2").map(_.value) == Right("2"))
    val _ = assert(term.parseAll("1*2").map(_.value) == Right("(1*2)"))
    val _ = assert(expr.parseAll("2+1").map(_.value) == Right("(2+1)"))
    val _ = assert(expr.parseAll("1*2+1").map(_.value) == Right("((1*2)+1)"))
    val _ = assert(term.parseAll("1*2+1*2").map(_.value) == Right("(((1*2)+1)*2)"))
  }

  test("recursive supports a triple of mutually left-recursive parsers") {
    import StrictParser.*

    // E -> T '+' '1' | '1'
    // T -> F '*' '2' | '2'
    // F -> E '/' '3' | '3'
    def step(rec: P[Unit, String], op: String, operand: String): P[Unit, String] = {
      (rec <* literal(op) && literal(operand)).map(Fn.lift((l, r) => s"($l$op$r)")) |> literal(operand)
    }
    val (expr, term, fact) = recursive[(P[Unit, String], P[Unit, String], P[Unit, String])] { (recE, recT, recF) =>
      (step(recT, "+", "1"), step(recF, "*", "2"), step(recE, "/", "3"))
    }
    val _ = assert(expr.parseAll("1").map(_.value) == Right("1"))
    val _ = assert(term.parseAll("2").map(_.value) == Right("2"))
    val _ = assert(fact.parseAll("3").map(_.value) == Right("3"))
    val _ = assert(fact.parseAll("1/3").map(_.value) == Right("(1/3)"))
    val _ = assert(term.parseAll("3*2").map(_.value) == Right("(3*2)"))
    val _ = assert(expr.parseAll("2+1").map(_.value) == Right("(2+1)"))
    val _ = assert(expr.parseAll("3*2+1").map(_.value) == Right("((3*2)+1)"))
    val _ = assert(expr.parseAll("1/3*2+1").map(_.value) == Right("(((1/3)*2)+1)"))
    val _ = assert(fact.parseAll("3*2+1/3").map(_.value) == Right("(((3*2)+1)/3)"))
    val _ = assert(expr.parseAll("1/3*2+1/3*2+1").map(_.value) == Right("((((((1/3)*2)+1)/3)*2)+1)"))
  }

  // =========================================================================
  // Agreement with the reference interpreter
  // =========================================================================

  import ParserAlgebra.Standard

  /** A grammar written once against any standard algebra, given a way to embed functions. */
  trait Grammar[B] {
    def apply(alg: Standard)(lift: [X, Y] => (X => Y) => alg.On[X, Y]): alg.P[Unit, B]
  }

  private val inputs = List("", "a", "b", "ab", "aab", "aaab", "abab", "a,a,a", "a,a,", "(a)", "((a))", "((a)", "[1, 22]")

  private def agree[B](name: String)(grammar: Grammar[B])(using CanEqual[B, B]): Unit = {
    test(s"StrictParser agrees with ReferenceParser on $name") {
      val reference = grammar(ReferenceParser)([X, Y] => (f: X => Y) => f)
      val strict    = grammar(StrictParser)([X, Y] => (f: X => Y) => Fn.lift(f))
      for input <- inputs do {
        val expected = ReferenceParser.parse(reference)(input) match {
          case ReferenceParser.Result.Success(value, offset) => Some((value, offset))
          case ReferenceParser.Result.Failure(_, _)          => None
        }
        val actual = StrictParser.parse(strict)(input).toOption.map(r => (r.value, r.offset))
        val _ = assert(actual == expected, s"on input \"$input\"")
      }
    }
  }

  agree("sequencing")(new Grammar[(String, String)] {
    def apply(alg: Standard)(lift: [X, Y] => (X => Y) => alg.On[X, Y]) = {
      import alg.*
      (literal("a") *> literal("a")) && (literal("a") |> literal("b")).between(success[Unit], literal("b").not)
    }
  })

  agree("choice and lookahead")(new Grammar[Either[Either[String, String], Unit]] {
    def apply(alg: Standard)(lift: [X, Y] => (X => Y) => alg.On[X, Y]) = {
      import alg.*
      ((literal("a") <* ~literal("b")) +> literal("b")).optional
    }
  })

  agree("iteration")(new Grammar[(Vector[String], (Vector[String], Vector[String]))] {
    def apply(alg: Standard)(lift: [X, Y] => (X => Y) => alg.On[X, Y]) = {
      import alg.*
      val a = literal("a")
      ~a.times(1) *> (a.atLeast(1).pair(literal(",").repeated.pair(a.separatedBy(literal(",")).optional.map(
        lift(_.fold(identity, _ => Vector.empty))
      ))) |> pure(lift(_ => (Vector.empty, (Vector.empty, Vector.empty)))))
    }
  })

  agree("merge and loop")(new Grammar[Int] {
    def apply(alg: Standard)(lift: [X, Y] => (X => Y) => alg.On[X, Y]) = {
      import alg.*
      val step: P[Int, Either[Int, Int]] =
        literal("a").mapInput(lift((_: Int) => ())).pair(success[Int]).map(lift((_, n) => Right(n + 1))) |>
          pure(lift(Left(_)))
      (literal("b") +> success[Unit]).andThen(pure(lift((_: String) => 100)) || pure(lift(_ => 0))).andThen(step.loop)
    }
  })

  agree("recursion")(new Grammar[(Int, List[Int])] {
    def apply(alg: Standard)(lift: [X, Y] => (X => Y) => alg.On[X, Y]) = {
      import alg.*
      val nested = recursive[Unit, Int] { self =>
        literal("a").map(lift(_ => 0)) |> self.between(literal("("), literal(")")).map(lift(_ + 1))
      }
      val number = regex("[0-9]+".r).map(lift(_.toInt))
      val list   = number.separatedBy(regex(", *".r)).between(literal("["), literal("]")).map(lift(_.toList))
      (nested +> list).map(lift(_.fold((_, Nil), (-1, _))))
    }
  })
}
