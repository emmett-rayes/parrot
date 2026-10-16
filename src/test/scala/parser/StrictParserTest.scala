package parrot
package parser

import category.*
import org.scalacheck.{Arbitrary, Gen, Prop, Test}

class StrictParserTest extends CategorySuite {
  import StrictParserTest.*
  import parser.*
  import parser.Node.*

  given CanEqual[Any, Any] = CanEqual.derived

  test("StrictParser fuses the generic Concatenation derivations into dedicated nodes") {
    val a = literal("a")
    val b = literal("b")
    val c = literal("c")

    val _ = assert((a && b) == Pair(Literal("a"), Literal("b")))
    val _ = assert((a *> b) == SkipThen(Literal("a"), Literal("b")))
    val _ = assert((a <* b) == ThenSkip(Literal("a"), Literal("b")))
    val _ = assert(b.between(a, c) == ThenSkip(SkipThen(Literal("a"), Literal("b")), Literal("c")))
  }

  test("StrictParser fuses branching and zipping with success") {
    val a = literal("a")
    val b = literal("b")

    val _ = assert((a || b) == Merge(Literal("a"), Literal("b")))
    val _ = assert(a.zip(success[Int]) == Zip(Literal("a"), Success()))
  }

  test("StrictParser eliminates identities and fuses pure morphisms") {
    val a = literal("a")
    val f = Fn.lift((s: String) => s.length)

    val _ = assert((success[Unit] >> a >> success[String]) == Literal("a"))
    val _ = assert(pure(Fn.id[Int]) == Success[Int]())
    val _ = assert(a.map(Fn.id[String]) == Literal("a"))
    val _ = assert(a.map(f).map(Fn.lift((n: Int) => n + 1)).isInstanceOf[Seq[?, ?, ?]])
    val _ = assert((a && a).map(OnIsCartesian.first).map(f) == Seq(ThenSkip(Literal("a"), Literal("a")), Pure(f)))
  }

  test("StrictParser flattens choices and distributes pure functions over them") {
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
    val _ = assert(regex("[0-9]+".r).isInstanceOf[Scan])
    val _ = assert(regex("[1-9][0-9]*".r).isInstanceOf[Scan])
    val _ = assert(regex("[^\"\\\\\\u0000-\\u001f]+".r).isInstanceOf[Scan])
    val _ = assert(regex("a*a".r).isInstanceOf[Pattern])
    val _ = assert(regex("(ab)+".r).isInstanceOf[Pattern])
  }

  test("StrictParser dispatches choices on the next character") {
    val keyword = literal("true") |> literal("false") |> literal("null") |> regex("[0-9]+".r)
    val _       = assert(keyword.parse("null").map(_.result) == scala.util.Success("null"))
    val _       = assert(keyword.parse("42").map(_.result) == scala.util.Success("42"))
    val _       = assert(keyword.parse("x") == scala.util.Failure(ParseError(0, "\"true\"")))
    val _       = assert(keyword.parse("") == scala.util.Failure(ParseError(0, "\"true\"")))
    val _       = assert((literal("") |> literal("a")).parse("a").map(_.offset) == scala.util.Success(0))
  }

  test("recursive supports direct left recursion and grows the seed") {
    val expr = recursive[Unit, String] { rec =>
      (rec <* literal("+") && literal("1")).map(Fn.lift((e, one) => s"($e+$one)")) |> literal("1")
    }
    val _ = assert(expr.parse("1").map(_.result) == scala.util.Success("1"))
    val _ = assert(expr.parse("1+1").map(_.result) == scala.util.Success("(1+1)"))
    val _ = assert(expr.parse("1+1+1").map(_.result) == scala.util.Success("((1+1)+1)"))
    val _ = assert(expr.parseAll("1+1+1+1").map(_.result) == scala.util.Success("(((1+1)+1)+1)"))
    val _ = assert(expr.parse("x").isFailure)
  }

  test("recursive supports non-left recursion") {
    val parens = recursive[Unit, String] { rec =>
      rec.between(literal("("), literal(")")).map(Fn.lift(inner => s"[$inner]")) |> literal("x")
    }
    val _ = assert(parens.parseAll("x").map(_.result) == scala.util.Success("x"))
    val _ = assert(parens.parseAll("(x)").map(_.result) == scala.util.Success("[x]"))
    val _ = assert(parens.parseAll("((x))").map(_.result) == scala.util.Success("[[x]]"))
  }

  test("recursive supports semantic input (e.g. a left-associative accumulator)") {
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
    val (expr, term) = recursive[(P[Unit, String], P[Unit, String])] { (recE, recT) =>
      val e = (recT <* literal("+") && literal("1")).map(Fn.lift((t, one) => s"($t+$one)")) |> literal("1")
      val t = (recE <* literal("*") && literal("2")).map(Fn.lift((e, two) => s"($e*$two)")) |> literal("2")
      (e, t)
    }
    val _ = assert(expr.parseAll("1").map(_.result) == scala.util.Success("1"))
    val _ = assert(term.parseAll("2").map(_.result) == scala.util.Success("2"))
    val _ = assert(term.parseAll("1*2").map(_.result) == scala.util.Success("(1*2)"))
    val _ = assert(expr.parseAll("2+1").map(_.result) == scala.util.Success("(2+1)"))
    val _ = assert(expr.parseAll("1*2+1").map(_.result) == scala.util.Success("((1*2)+1)"))
    val _ = assert(term.parseAll("1*2+1*2").map(_.result) == scala.util.Success("(((1*2)+1)*2)"))
  }

  test("recursive supports a triple of mutually left-recursive parsers") {
    def step(rec: P[Unit, String], op: String, operand: String): P[Unit, String] = {
      (rec <* literal(op) && literal(operand)).map(Fn.lift((l, r) => s"($l$op$r)")) |> literal(operand)
    }
    val (expr, term, fact) = recursive[(P[Unit, String], P[Unit, String], P[Unit, String])] { (recE, recT, recF) =>
      (step(recT, "+", "1"), step(recF, "*", "2"), step(recE, "/", "3"))
    }
    val _ = assert(expr.parseAll("1").map(_.result) == scala.util.Success("1"))
    val _ = assert(term.parseAll("2").map(_.result) == scala.util.Success("2"))
    val _ = assert(fact.parseAll("3").map(_.result) == scala.util.Success("3"))
    val _ = assert(fact.parseAll("1/3").map(_.result) == scala.util.Success("(1/3)"))
    val _ = assert(term.parseAll("3*2").map(_.result) == scala.util.Success("(3*2)"))
    val _ = assert(expr.parseAll("2+1").map(_.result) == scala.util.Success("(2+1)"))
    val _ = assert(expr.parseAll("3*2+1").map(_.result) == scala.util.Success("((3*2)+1)"))
    val _ = assert(expr.parseAll("1/3*2+1").map(_.result) == scala.util.Success("(((1/3)*2)+1)"))
    val _ = assert(fact.parseAll("3*2+1/3").map(_.result) == scala.util.Success("(((3*2)+1)/3)"))
    val _ = assert(expr.parseAll("1/3*2+1/3*2+1").map(_.result) == scala.util.Success("((((((1/3)*2)+1)/3)*2)+1)"))
  }

  import StrictParserTest.*

  private val referenceParser = new ReferenceParser {}
  private val inputs = List("", "a", "b", "ab", "aab", "aaab", "abab", "a,a,a", "a,a,", "(a)", "((a))", "((a)", "[1, 22]")

  private def agree[B](name: String)(grammar: Grammar[B])(using CanEqual[B, B]): Unit = {
    test(s"StrictParser agrees with ReferenceParser on $name") {
      val reference = grammar(referenceParser)([X, Y] => (f: X => Y) => f)
      val strict    = grammar(parser)([X, Y] => (f: X => Y) => Fn.lift(f))
      for input <- inputs do {
        val expected = referenceParser.parse(reference)(input).toOption
        val actual   = strict.parse(input).toOption
        val _        = assert(actual == expected, s"StrictParser on input \"$input\"")
      }
    }
  }

  agree("sequencing")(sequencingGrammar)
  agree("choice and lookahead")(choiceAndLookaheadGrammar)
  agree("iteration")(iterationGrammar)
  agree("merge and loop")(mergeAndLoopGrammar)
  agree("recursion")(recursionGrammar)

  private val sources = {
    Gen.oneOf("", "a", "b", "c", "aa", "ab", "ba", "abc", "aab", "abab", "aaab", "bba", "(a)", "((a))", "[(a)]")
  }

  private def runExt[A, B](p: P[A, B], a: A, source: String): Option[(B, Int)] = {
    val state = State(source)
    val out   = p.run(a, state)
    Option.when(!out.isFailed)((out.get, state.offset))
  }

  /** Equal results and offsets on sampled semantic inputs and sources. */
  private given NodeIsEq: [A: Arbitrary, B: Eq] => (P[A, B] is Eq) = new (P[A, B] is Eq) {
    def eq(p: P[A, B], q: P[A, B]): Boolean = {
      val prop = Prop.forAll(Arbitrary.arbitrary[A], sources) { (a, source) =>
        (runExt(p, a, source), runExt(q, a, source)) match {
          case (Some((x, i)), Some((y, j))) => x === y && i == j
          case (scala.None, scala.None)     => true
          case _                            => false
        }
      }
      Test.check(Test.Parameters.default.withMinSuccessfulTests(50), prop).passed
    }
  }

  private def liftFn[A, B](f: A => B): Fn[A, B] = Fn.lift(f)

  private val aLit = literal("a")
  private val bLit = literal("b")

  /** Consumes "a" on multiples of 3, otherwise succeeds without consuming. */
  private val pLaw: P[Int, String] = {
    pure(liftFn((i: Int) => if i % 3 == 0 then Left(()) else Right(i))) >> (aLit || pure(liftFn(i => s"v$i")))
  }

  /** Consumes "b", then tests the semantic input, or fails. */
  private val qLaw: P[String, Boolean] = (bLit.mapInput(Fn.Bang[String]()) *> success[String]).map(liftFn(_.length > 1))

  /** Consumes "a" on `true`, fails on `false`. */
  private val rLaw: P[Boolean, Int] = {
    pure(liftFn((x: Boolean) => if x then Left(()) else Right(()))) >> (aLit.map(liftFn(_ => 1)) || failure[Unit, Int])
  }

  /** Consumes "b" and tests parity, or falls back to testing the sign. */
  private val sLaw: P[Int, Boolean] = {
    (bLit.mapInput(Fn.Bang[Int]()) *> success[Int]).map(liftFn(_ % 2 == 0)) |> pure(liftFn(_ > 0))
  }

  /** Consumes "a" and counts down, stopping at 0 or when there is no "a". */
  private val countdownLaw: P[Int, Either[String, Int]] = {
    val step = liftFn((n: Int) => if n <= 0 then Left(s"done$n") else Right(n - 1))
    (aLit.mapInput(Fn.Bang[Int]()) *> success[Int]).map(step) |> pure(liftFn(n => Left(s"stop$n")))
  }

  private given Arbitrary[P[Int, String]] = Arbitrary {
    Gen.oneOf(pLaw, sLaw.map(liftFn(_.toString)), failure[Int, String], countdownLaw.map(liftFn(_.toString)))
  }

  test("the extensional equality distinguishes parsers") {
    val eq = summon[P[Int, String] is Eq]
    val _  = assert(eq.eq(pLaw, pLaw))
    val _  = assert(!eq.eq(pLaw, pLaw.map(liftFn(_ + "!"))))
    val _  = assert(!eq.eq(pLaw, pLaw <* bLit.mapInput(Fn.Bang[Int]())))
    assert(!eq.eq(pLaw, failure))
  }

  private val PromonadInst = NodeIsPromonad

  test("StrictParser is Promonad: identity, associativity and naturality") {
    val laws = PromonadInst.PromonadLaws
    val _    = assert(laws.leftIdentity(pLaw))
    val _    = assert(laws.rightIdentity(pLaw))
    val _    = assert(laws.associativity(pLaw, qLaw, rLaw))
    val h    = liftFn((x: Boolean) => if x then 1 else 2)
    val _    = assert(laws.unitNaturality(liftFn((i: Int) => s"$i"), h, liftFn(_.length)))
    assert(laws.multiplicationNaturality(pLaw, qLaw, h, liftFn((x: Boolean) => !x)))
  }

  private val StrongInst = NodeIsStrong

  test("StrictParser is Strong: unitality, associativity and naturality") {
    val laws = StrongInst.StrongLaws
    val _    = assert(laws.firstUnitality(pLaw))
    val _    = assert(laws.secondUnitality(pLaw))
    val _    = assert(laws.firstAssociativity[Int, String, Boolean, Int](pLaw))
    val _    = assert(laws.secondAssociativity[Int, String, Boolean, Int](pLaw))
    val f    = liftFn((x: Boolean) => if x then 3 else 4)
    val g    = liftFn((s: String) => s.length)
    val _    = assert(laws.firstNaturality[Int, String, Boolean, Int, Int](pLaw, f, g))
    assert(laws.secondNaturality[Int, String, Boolean, Int, Int](pLaw, f, g))
  }

  test("StrictParser is premonoidal, not monoidal: interchange fails") {
    val ab = StrongInst.first[Unit, String, Unit](aLit) >> StrongInst.second[Unit, String, String](bLit)
    val ba = StrongInst.second[Unit, String, Unit](bLit) >> StrongInst.first[Unit, String, String](aLit)
    val _  = assert(runExt(ab, ((), ()), "ab") == Some((("a", "b"), 2)))
    assert(runExt(ba, ((), ()), "ab") == scala.None)
  }

  private val CocartesianInst = NodeIsCocartesian

  test("StrictParser is Cocartesian: injections, copairing and folds") {
    val laws = CocartesianInst.CocartesianLaws
    val g    = rLaw.map(liftFn(_.toString))
    val _    = assert(laws.leftInjection(pLaw, g))
    val _    = assert(laws.rightInjection(pLaw, g))
    val _    = assert(laws.sumUniqueness[Int, String])
    val _    = assert(laws.foldLeft[String])
    assert(laws.foldRight[Int])
  }

  private val AdditiveInst = NodeIsAdditiveEnriched

  test("StrictParser is Enriched over additive monoids: monoid laws") {
    val laws = AdditiveInst.HomIsV[Int, String].MonoidLaws
    val _    = assert(laws.leftIdentity)
    val _    = assert(laws.rightIdentity)
    assert(laws.associativity)
  }

  test("StrictParser is Enriched over additive monoids: homomorphy, annihilation and right distributivity") {
    import AdditiveInst.given
    val laws  = AdditiveInst.MonoidEnrichedLaws
    val twice = liftFn((i: Int) => i * 2)
    val shout = liftFn((x: String) => x + "!")
    val _     = assert(laws.unitHomomorphy[Int, String, Int, String, Function, Unit, Tuple2](twice, shout))
    val _     = assert(laws.multiplicationHomomorphy[Int, String, Int, String, Function, Unit, Tuple2](twice, shout))
    val _     = assert(laws.rightDistributivity[Int, Int, String, Function, Unit, Tuple2](pure(liftFn(_ + 1))))
    val _     = assert(
      laws.rightDistributivity[Int, Int, String, Function, Unit, Tuple2](aLit.mapInput(Fn.Bang[Int]()) *> success[Int])
    )
    assert(laws.unitAnnihilation[Int, String, Int, Function, Unit, Tuple2](qLaw.map(liftFn(x => if x then 1 else 0)), pLaw))
  }

  test("StrictParser is Enriched over additive monoids: left distributivity fails") {
    val c     = literal("c")
    val left  = (literal("a") |> literal("ab")) >> c.mapInput(Fn.Bang[String]())
    val right = (literal("a") >> c.mapInput(Fn.Bang[String]())) |> (literal("ab") >> c.mapInput(Fn.Bang[String]()))
    val _     = assert(runExt(left, (), "abc") == scala.None)
    assert(runExt(right, (), "abc") == Some(("c", 3)))
  }

  private val RestrictionInst = NodeIsRestriction

  test("StrictParser is Restriction: lookahead satisfies the restriction laws") {
    val laws = RestrictionInst.RestrictionLaws
    val _    = assert(laws.restrictionIdentity(pLaw))
    val _    = assert(laws.restrictionCommutativity(pLaw, sLaw))
    val _    = assert(laws.restrictionCompose(pLaw, sLaw))
    assert(laws.restrictionPrecompose(pLaw, qLaw))
  }

  private val ElgotInst = NodeIsElgot

  test("StrictParser is Elgot: loop satisfies the iteration laws") {
    val laws = ElgotInst.ElgotLaws
    val nested: P[Int, Either[Either[String, Int], Int]] = {
      (aLit.mapInput(Fn.Bang[Int]()) *> success[Int]).map(liftFn(n => Left(Right(n - 1)))) |>
        (bLit.mapInput(Fn.Bang[Int]()) *> success[Int]).map(liftFn(n => Right(n + 1))) |>
        pure(liftFn(n => Left(Left(s"stop$n"))))
    }
    val _ = assert(runExt(ElgotInst.dagger(countdownLaw), 1, "aaa") == Some(("done0", 2)))
    val _ = assert(laws.fixedPoint(countdownLaw))
    val _ = assert(laws.parameterNaturality(countdownLaw, liftFn(_.length)))
    val _ = assert(laws.composition[String, Int, Int](countdownLaw, liftFn(_ * 2)))
    assert(laws.doubleDagger(nested))
  }

  private val RecursionInst = NodeIsFixedEnriched

  private val nestedLaw: P[Unit, String] => P[Unit, String] = self => aLit |> self.between(literal("("), literal(")"))

  test("StrictParser is Enriched over Fixed: recursion in hom-sets") {
    val fixed = RecursionInst.HomIsV[Unit, String].fix(nestedLaw)
    val _     = assert(runExt(fixed, (), "a") == Some(("a", 1)))
    val _     = assert(runExt(fixed, (), "(a)") == Some(("a", 3)))
    assert(runExt(fixed, (), "((a))") == Some(("a", 5)))
  }

  test("StrictParser is Enriched over Fixed: seed growing breaks the fixed-point law under left recursion") {
    val expr: P[Unit, String] => P[Unit, String] = self => {
      (self <* literal("+") && literal("1")).map(liftFn((e, one) => s"($e+$one)")) |> literal("1")
    }
    val fixed = RecursionInst.HomIsV[Unit, String].fix(expr)
    val _     = assert(runExt(fixed, (), "1+1+1") == Some(("((1+1)+1)", 5)))
    assert(runExt(expr(fixed), (), "1+1+1") == Some(("1", 1)))
  }

  test("StrictParser satisfies the ParserLaws") {
    val laws    = ParserLaws
    val samples = List(aLit, bLit, aLit *> bLit, aLit |> bLit, aLit.repeated.map(liftFn(_.mkString)), failure[Unit, String])
    for x <- samples; y <- samples do {
      val _ = assert(laws.leftIdentity(x))
      val _ = assert(laws.rightIdentity(x))
      val _ = assert(laws.choiceAssociativity(x, y, aLit))
      val _ = assert(laws.lookaheadCommutativity(x, y))
      val _ = assert(laws.lookaheadCompose(x, y))
      val _ = assert(laws.doubleNegation(x))
      val _ = assert(laws.negationExclusion(x))
    }
    val _ = assert(laws.zipIdentity[Unit, Int])
    val _ = assert(laws.loopUnfolding(countdownLaw))
    assert(laws.recursionUnfolding(nestedLaw))
  }
}

object StrictParserTest {
  val parser: StrictParser = new StrictParser {}

  trait Grammar[B] {
    def apply(alg: ParserAlgebra.Standard)(lift: [X, Y] => (X => Y) => alg.On[X, Y]): alg.P[Unit, B]
  }

  val sequencingGrammar: Grammar[(String, String)] = new Grammar[(String, String)] {
    def apply(alg: ParserAlgebra.Standard)(lift: [X, Y] => (X => Y) => alg.On[X, Y]) = {
      import alg.*
      (literal("a") *> literal("a")) && (literal("a") |> literal("b")).between(success[Unit], literal("b").not)
    }
  }

  val choiceAndLookaheadGrammar: Grammar[Either[Either[String, String], Unit]] =
    new Grammar[Either[Either[String, String], Unit]] {
      def apply(alg: ParserAlgebra.Standard)(lift: [X, Y] => (X => Y) => alg.On[X, Y]) = {
        import alg.*
        ((literal("a") <* ~literal("b")) +> literal("b")).optional
      }
    }

  val iterationGrammar: Grammar[(Vector[String], (Vector[String], Vector[String]))] =
    new Grammar[(Vector[String], (Vector[String], Vector[String]))] {
      def apply(alg: ParserAlgebra.Standard)(lift: [X, Y] => (X => Y) => alg.On[X, Y]) = {
        import alg.*
        val a = literal("a")
        ~a.times(1) *> (a.atLeast(1).pair(literal(",").repeated.pair(a.separatedBy(literal(",")).optional.map(
          lift(_.fold(identity, _ => Vector.empty))
        ))) |> pure(lift(_ => (Vector.empty, (Vector.empty, Vector.empty)))))
      }
    }

  val mergeAndLoopGrammar: Grammar[Int] = new Grammar[Int] {
    def apply(alg: ParserAlgebra.Standard)(lift: [X, Y] => (X => Y) => alg.On[X, Y]) = {
      import alg.*
      val step: P[Int, Either[Int, Int]] =
        literal("a").mapInput(lift((_: Int) => ())).pair(success[Int]).map(lift((_, n) => Right(n + 1))) |>
          pure(lift(Left(_)))
      (literal("b") +> success[Unit]).andThen(pure(lift((_: String) => 100)) || pure(lift(_ => 0))).andThen(step.iterate)
    }
  }

  val recursionGrammar: Grammar[(Int, List[Int])] = new Grammar[(Int, List[Int])] {
    def apply(alg: ParserAlgebra.Standard)(lift: [X, Y] => (X => Y) => alg.On[X, Y]) = {
      import alg.*
      val nested = recursive[Unit, Int] { self =>
        literal("a").map(lift(_ => 0)) |> self.between(literal("("), literal(")")).map(lift(_ + 1))
      }
      val number = regex("[0-9]+".r).map(lift(_.toInt))
      val list   = number.separatedBy(regex(", *".r)).between(literal("["), literal("]")).map(lift(_.toList))
      (nested +> list).map(lift(_.fold((_, Nil), (-1, _))))
    }
  }
}
