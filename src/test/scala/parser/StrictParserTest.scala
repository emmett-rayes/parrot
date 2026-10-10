package parrot
package parser

import org.scalatest.funsuite.AnyFunSuite

class StrictParserTest extends AnyFunSuite {

  given CanEqual[StrictParser.Node[?, ?], StrictParser.Node[?, ?]] = CanEqual.derived

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

  // =========================================================================
  // Agreement with the reference interpreter
  // =========================================================================

  /** An algebra interpreted on the standard objects of **Type**. */
  type Standard = ParserAlgebra {
    type Empty             = Unit
    type Pair[A, B]        = (A, B)
    type Alternative[A, B] = Either[A, B]
    type Many[B]           = Vector[B]
  }

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

  given CanEqual[Unit, Unit] = CanEqual.derived

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
