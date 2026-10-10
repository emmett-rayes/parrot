package parrot
package parser

import parrot.category.{CategorySuite, Eq}

import org.scalacheck.{Arbitrary, Gen, Prop, Test}

/** Checks the laws of the categorical structures of [[StrictParser]], the same ones as for [[ReferenceParser]].
  *
  * Parsers are compared extensionally, by running them on sampled semantic inputs and sources.
  */
class StrictParserLawsTest extends CategorySuite {
  import StrictParser.*

  given CanEqual[Unit, Unit]       = CanEqual.derived
  given CanEqual[Boolean, Boolean] = CanEqual.derived
  given [A, B] => CanEqual[(A, B), (A, B)]             = CanEqual.derived
  given [A, B] => CanEqual[Either[A, B], Either[A, B]] = CanEqual.derived

  private val sources = {
    Gen.oneOf("", "a", "b", "c", "aa", "ab", "ba", "abc", "aab", "abab", "aaab", "bba", "(a)", "((a))", "[(a)]")
  }

  private def run[A, B](p: P[A, B], a: A, source: String): Option[(B, Int)] = {
    val state = State(source)
    val out   = p.run(a, state)
    Option.when(!out.isFailed)((out.get, state.offset))
  }

  /** Equal results and offsets on sampled semantic inputs and sources. */
  given NodeIsEq: [A: Arbitrary, B: Eq] => P[A, B] is Eq = new (P[A, B] is Eq) {
    def eq(p: P[A, B], q: P[A, B]): Boolean = {
      val prop = Prop.forAll(Arbitrary.arbitrary[A], sources) { (a, source) =>
        (run(p, a, source), run(q, a, source)) match {
          case (Some((x, i)), Some((y, j))) => x === y && i == j
          case (scala.None, scala.None)     => true
          case _                            => false
        }
      }
      Test.check(Test.Parameters.default.withMinSuccessfulTests(50), prop).passed
    }
  }

  private def lift[A, B](f: A => B): Fn[A, B] = Fn.lift(f)

  private val a = literal("a")
  private val b = literal("b")

  /** Consumes "a" on multiples of 3, otherwise succeeds without consuming. */
  private val p: P[Int, String] = {
    pure(lift((i: Int) => if i % 3 == 0 then Left(()) else Right(i))) >> (a || pure(lift(i => s"v$i")))
  }

  /** Consumes "b", then tests the semantic input, or fails. */
  private val q: P[String, Boolean] = (b.mapInput(Fn.Bang[String]()) *> success[String]).map(lift(_.length > 1))

  /** Consumes "a" on `true`, fails on `false`. */
  private val r: P[Boolean, Int] = {
    pure(lift((x: Boolean) => if x then Left(()) else Right(()))) >> (a.map(lift(_ => 1)) || failure[Unit, Int])
  }

  /** Consumes "b" and tests parity, or falls back to testing the sign. */
  private val s: P[Int, Boolean] = {
    (b.mapInput(Fn.Bang[Int]()) *> success[Int]).map(lift(_ % 2 == 0)) |> pure(lift(_ > 0))
  }

  /** Consumes "a" and counts down, stopping at 0 or when there is no "a". */
  private val countdown: P[Int, Either[String, Int]] = {
    val step = lift((n: Int) => if n <= 0 then Left(s"done$n") else Right(n - 1))
    (a.mapInput(Fn.Bang[Int]()) *> success[Int]).map(step) |> pure(lift(n => Left(s"stop$n")))
  }

  given Arbitrary[P[Int, String]] = Arbitrary {
    Gen.oneOf(p, s.map(lift(_.toString)), failure[Int, String], countdown.map(lift(_.toString)))
  }

  test("the extensional equality distinguishes parsers") {
    val eq = summon[P[Int, String] is Eq]
    val _  = assert(eq.eq(p, p))
    val _  = assert(!eq.eq(p, p.map(lift(_ + "!"))))
    val _  = assert(!eq.eq(p, p <* b.mapInput(Fn.Bang[Int]())))
    assert(!eq.eq(p, failure))
  }

  // =========================================================================
  // Promonad
  // =========================================================================

  private val Promonad = StrictParser.NodeIsPromonad

  test("StrictParser is Promonad: identity, associativity and naturality") {
    val laws = Promonad.PromonadLaws
    val _    = assert(laws.leftIdentity(p))
    val _    = assert(laws.rightIdentity(p))
    val _    = assert(laws.associativity(p, q, r))
    val h    = lift((x: Boolean) => if x then 1 else 2)
    val _    = assert(laws.unitNaturality(lift((i: Int) => s"$i"), h, lift(_.length)))
    assert(laws.multiplicationNaturality(p, q, h, lift((x: Boolean) => !x)))
  }

  // =========================================================================
  // Strong (premonoidal)
  // =========================================================================

  private val Strong = StrictParser.NodeIsStrong

  test("StrictParser is Strong: unitality, associativity and naturality") {
    val laws = Strong.StrongLaws
    val _    = assert(laws.firstUnitality(p))
    val _    = assert(laws.secondUnitality(p))
    val _    = assert(laws.firstAssociativity[Int, String, Boolean, Int](p))
    val _    = assert(laws.secondAssociativity[Int, String, Boolean, Int](p))
    val f    = lift((x: Boolean) => if x then 3 else 4)
    val g    = lift((s: String) => s.length)
    val _    = assert(laws.firstNaturality[Int, String, Boolean, Int, Int](p, f, g))
    assert(laws.secondNaturality[Int, String, Boolean, Int, Int](p, f, g))
  }

  test("StrictParser is premonoidal, not monoidal: interchange fails") {
    val ab = Strong.first[Unit, String, Unit](a) >> Strong.second[Unit, String, String](b)
    val ba = Strong.second[Unit, String, Unit](b) >> Strong.first[Unit, String, String](a)
    val _  = assert(run(ab, ((), ()), "ab") == Some((("a", "b"), 2)))
    assert(run(ba, ((), ()), "ab") == scala.None)
  }

  // =========================================================================
  // Cocartesian
  // =========================================================================

  private val Cocartesian = StrictParser.NodeIsCocartesian

  test("StrictParser is Cocartesian: injections, copairing and folds") {
    val laws = Cocartesian.CocartesianLaws
    val g    = r.map(lift(_.toString))
    val _    = assert(laws.leftInjection(p, g))
    val _    = assert(laws.rightInjection(p, g))
    val _    = assert(laws.sumUniqueness[Int, String])
    val _    = assert(laws.foldLeft[String])
    assert(laws.foldRight[Int])
  }

  // =========================================================================
  // Enriched over additive monoids (ordered choice)
  // =========================================================================

  private val Additive = StrictParser.NodeIsAdditiveEnriched

  test("StrictParser is Enriched over additive monoids: monoid laws") {
    val laws = Additive.HomIsV[Int, String].MonoidLaws
    val _    = assert(laws.leftIdentity)
    val _    = assert(laws.rightIdentity)
    assert(laws.associativity)
  }

  test("StrictParser is Enriched over additive monoids: homomorphy, annihilation and right distributivity") {
    import Additive.given
    val laws  = Additive.MonoidEnrichedLaws
    val twice = lift((i: Int) => i * 2)
    val shout = lift((x: String) => x + "!")
    val _     = assert(laws.unitHomomorphy[Int, String, Int, String, Function, Unit, Tuple2](twice, shout))
    val _     = assert(laws.multiplicationHomomorphy[Int, String, Int, String, Function, Unit, Tuple2](twice, shout))
    val _     = assert(laws.rightDistributivity[Int, Int, String, Function, Unit, Tuple2](pure(lift(_ + 1))))
    val _     = assert(
      laws.rightDistributivity[Int, Int, String, Function, Unit, Tuple2](a.mapInput(Fn.Bang[Int]()) *> success[Int])
    )
    assert(laws.unitAnnihilation[Int, String, Int, Function, Unit, Tuple2](q.map(lift(x => if x then 1 else 0)), p))
  }

  test("StrictParser is Enriched over additive monoids: left distributivity fails") {
    // (a | ab) ⨾ c commits to "a" and then fails on "bc", whereas a ⨾ c | ab ⨾ c succeeds
    val c     = literal("c")
    val left  = (literal("a") |> literal("ab")) >> c.mapInput(Fn.Bang[String]())
    val right = (literal("a") >> c.mapInput(Fn.Bang[String]())) |> (literal("ab") >> c.mapInput(Fn.Bang[String]()))
    val _     = assert(run(left, (), "abc") == scala.None)
    assert(run(right, (), "abc") == Some(("c", 3)))
  }

  // =========================================================================
  // Restriction
  // =========================================================================

  private val Restriction = StrictParser.NodeIsRestriction

  test("StrictParser is Restriction: lookahead satisfies the restriction laws") {
    val laws = Restriction.RestrictionLaws
    val _    = assert(laws.restrictionIdentity(p))
    val _    = assert(laws.restrictionCommutativity(p, s))
    val _    = assert(laws.restrictionCompose(p, s))
    assert(laws.restrictionPrecompose(p, q))
  }

  // =========================================================================
  // Elgot
  // =========================================================================

  private val Elgot = StrictParser.NodeIsElgot

  test("StrictParser is Elgot: loop satisfies the iteration laws") {
    val laws = Elgot.ElgotLaws
    // consumes "a" to go left, "b" to go right, and otherwise stops
    val nested: P[Int, Either[Either[String, Int], Int]] = {
      (a.mapInput(Fn.Bang[Int]()) *> success[Int]).map(lift(n => Left(Right(n - 1)))) |>
        (b.mapInput(Fn.Bang[Int]()) *> success[Int]).map(lift(n => Right(n + 1))) |>
        pure(lift(n => Left(Left(s"stop$n"))))
    }
    val _ = assert(run(Elgot.dagger(countdown), 1, "aaa") == Some(("done0", 2)))
    val _ = assert(laws.fixedPoint(countdown))
    val _ = assert(laws.parameterNaturality(countdown, lift(_.length)))
    val _ = assert(laws.composition[String, Int, Int](countdown, lift(_ * 2)))
    assert(laws.doubleDagger(nested))
  }

  // =========================================================================
  // Enriched over fixed points (recursion)
  // =========================================================================

  private val Recursion = StrictParser.NodeIsFixedEnriched

  /** nested ::= "a" | "(" nested ")" */
  private val nested: P[Unit, String] => P[Unit, String] = self => a |> self.between(literal("("), literal(")"))

  test("StrictParser is Enriched over Fixed: Conway laws for productive recursion") {
    val laws = Recursion.HomIsV[Unit, String].FixedLaws
    val _    = assert(laws.fixedPoint(nested))
    val _    = assert(laws.diagonal { (x, y) =>
      a |> x.between(literal("("), literal(")")) |> y.between(literal("["), literal("]"))
    })
    val _    = assert(
      laws.dinaturality[P[Unit, Int]](
        self => self.map(lift(_.length)),
        self => a |> self.map(lift(n => "x" * n)).between(literal("("), literal(")")),
      )(using Recursion.HomIsV[Unit, Int])
    )
    assert(
      Recursion.FixedEnrichedLaws.homDinaturality[Unit, String, Unit, Int](
        self => self.map(lift(_.length)),
        self => nested(self.map(lift(_.toString))),
      )(using Recursion.HomIsV[Unit, String], Recursion.HomIsV[Unit, Int])
    )
  }

  test("StrictParser is Enriched over Fixed: seed growing breaks the fixed-point law under left recursion") {
    // expr ::= expr "+" "1" | "1"
    val expr: P[Unit, String] => P[Unit, String] = self => {
      (self <* literal("+") && literal("1")).map(lift((e, one) => s"($e+$one)")) |> literal("1")
    }
    val fixed = Recursion.HomIsV[Unit, String].fix(expr)
    val _     = assert(run(fixed, (), "1+1+1") == Some(("((1+1)+1)", 5)))
    // the unfolding first grows the seed to the whole input, then cannot find a further "+"
    assert(run(expr(fixed), (), "1+1+1") == Some(("1", 1)))
  }

  // =========================================================================
  // Parser laws
  // =========================================================================

  test("StrictParser satisfies the ParserLaws") {
    val laws    = ParserLaws
    val samples = List(a, b, a *> b, a |> b, a.repeated.map(lift(_.mkString)), failure[Unit, String])
    for x <- samples; y <- samples do {
      val _ = assert(laws.leftIdentity(x))
      val _ = assert(laws.rightIdentity(x))
      val _ = assert(laws.choiceAssociativity(x, y, a))
      val _ = assert(laws.lookaheadCommutativity(x, y))
      val _ = assert(laws.lookaheadCompose(x, y))
      val _ = assert(laws.doubleNegation(x))
      val _ = assert(laws.negationExclusion(x))
    }
    val _ = assert(laws.zipIdentity[Unit, Int])
    val _ = assert(laws.loopUnfolding(countdown))
    assert(laws.recursionUnfolding(nested))
  }
}
