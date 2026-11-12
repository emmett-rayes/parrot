package parrot
package parser

import category.*
import org.scalacheck.Gen

import Sample.given

/** A grammar from semantic input `Int` to result `Int`, independent of interpreters: random grammars are generated once
  * and run on every interpreter.
  *
  * A [[Term.Family]] is a tuple of mutually recursive rules, of which the first is the grammar, and a [[Term.Call]]
  * is a call of a rule of the innermost enclosing family, which fails outside one. In an [[Term.Unguarded]] rule, the
  * recursive call follows a prefix that consumes nothing.
  */
enum Term derives CanEqual {
  case Lit(text: String)
  case Re(pattern: String)
  case Arith(seed: Int)
  case Fail
  case Then(p: Term, q: Term)
  case Alt(p: Term, q: Term)
  case Look(p: Term)
  case Neg(p: Term)
  case Both(p: Term, q: Term)
  case Try(p: Term, seed: Int)
  case Many(p: Term)
  case Exactly(p: Term, n: Int)
  case AtLeast(p: Term, n: Int)
  case SepBy(p: Term, separator: Term)
  case Loop(p: Term)
  case Nest(p: Term, open: String, close: String)
  case Named(label: String, p: Term)
  case Zipped(p: Term, q: Term)
  case Branched(p: Term, q: Term)
  case Tagged(p: Term, q: Term)
  case Opt(p: Term, seed: Int)
  case Maybe(p: Term, seed: Int)
  case Many1(p: Term)
  case Between(p: Term, open: Term, close: Term)
  case Pre(p: Term, seed: Int)
  case Call(rule: Int)
  case Family(rules: Vector[Term])
  case Unguarded(p: Term, prefix: Term)
}

object Grammars {
  import Term.*

  /** The parser denoted by `term` in `alg`. */
  def interpret(alg: ParserAlgebra)(term: Term): alg.P[Int, Int] = {
    import alg.*

    def arith(f: Int -> Int): P[Int, Int] = pure(lift(f))

    def text(p: P[Unit, String]): P[Int, Int] = {
      (p.mapInput(lift((_: Int) => ())) && success[Int]).map(lift((s, n) => n + s.length))
    }

    def within(family: Vector[P[Int, Int]]): Term -> P[Int, Int] = {
      def go(t: Term): P[Int, Int] = {
        t match {
          case Lit(s)        => text(literal(s))
          case Re(r)         => text(regex(r.r))
          case Arith(k)      => arith(n => n * 3 + k)
          case Fail          => failure[Int, Int]
          case Then(p, q)    => go(p) >> go(q)
          case Alt(p, q)     => go(p) |> go(q)
          case Look(p)       => ~go(p)
          case Neg(p)        => !go(p)
          case Both(p, q)    => (go(p) && go(q)).map(lift((x, y) => x * 31 + y))
          case Try(p, k)     => go(p).attempt >> (arith(_ + k) || arith(n => -n))
          case Many(p)       => go(p).repeated.map(lift(_.sum))
          case Exactly(p, n) => go(p).times(n).map(lift(_.sum))
          case AtLeast(p, n) => go(p).atLeast(n).map(lift(_.sum))
          case SepBy(p, sep) => go(p).separatedBy(go(sep)).map(lift(_.sum))
          case Loop(p)       =>
            val step = (go(p) && success[Int]).map(lift((x, n) => if n > 0 then Right((n - 1) % 4) else Left(x)))
            (step |> pure(lift[Int, Either[Int, Int]](Left(_)))).iterate
          case Nest(p, open, close) =>
            recursive[Int, Int](rec => go(p) |> (text(literal(open)) *> rec <* text(literal(close))))
          case Named(label, p) => go(p).rule(label)
          case Zipped(p, q)    =>
            (go(p) ** go(q)).mapInput(lift((n: Int) => (n, n + 1))).map(lift((x, y) => x * 31 + y))
          case Branched(p, q) =>
            (go(p) ++ go(q))
              .mapInput(lift[Int, Either[Int, Int]](n => if n % 2 == 0 then Left(n) else Right(n)))
              .map(lift(_.fold(x => x, y => -y)))
          case Tagged(p, q)           => (go(p) +> go(q)).map(lift(_.fold(x => x * 2, y => y * 2 + 1)))
          case Opt(p, k)              => go(p).optional.map(lift(_.fold(x => x + k, n => -n)))
          case Maybe(p, k)            => go(p).option.map(lift(_.fold(-k)(x => x + k)))
          case Many1(p)               => go(p).atLeastOnce.map(lift(_.sum))
          case Between(p, open, close) => go(p).between(go(open), go(close))
          case Pre(p, k)              => go(p).mapInput(lift((n: Int) => n * 2 + k))
          case Call(i)                => if family.isDefinedAt(i) then family(i) else failure[Int, Int]
          case Family(rules)          =>
            rules match {
              case Vector(r0, r1) =>
                recursive[(P[Int, Int], P[Int, Int])] { (p0, p1) =>
                  val rule = within(Vector(p0, p1))
                  (rule(r0), rule(r1))
                }._1
              case Vector(r0, r1, r2) =>
                recursive[(P[Int, Int], P[Int, Int], P[Int, Int])] { (p0, p1, p2) =>
                  val rule = within(Vector(p0, p1, p2))
                  (rule(r0), rule(r1), rule(r2))
                }._1
              case _ => failure[Int, Int]
            }
          case Unguarded(p, prefix) => recursive[Int, Int](rec => (go(prefix) >> rec) |> go(p))
        }
      }
      go
    }

    within(Vector.empty)(term)
  }

  /** A parser that consumes `text` and adds its length to the semantic input. */
  def consume(alg: ParserAlgebra)(text: String): alg.P[Int, Int] = {
    import alg.*
    (literal(text).mapInput(lift((_: Int) => ())) && success[Int]).map(lift((s, n) => n + s.length))
  }

  /** A guarded loop step: after consuming "a" it continues with half its input; otherwise it stops with `term`. */
  def step(alg: ParserAlgebra)(term: Term): alg.P[Int, Either[Int, Int]] = {
    import alg.*
    val next = consume(alg)("a").map(lift[Int, Either[Int, Int]](n => Right(n / 2)))
    next |> interpret(alg)(term).map(lift[Int, Either[Int, Int]](Left(_)))
  }

  /** A guarded grammar rule: `term`, or the rule itself between parentheses. */
  def nest(alg: ParserAlgebra)(term: Term): alg.P[Int, Int] -> alg.P[Int, Int] = {
    import alg.*
    rec => interpret(alg)(term) |> (consume(alg)("(") *> rec <* consume(alg)(")"))
  }

  /** The rules that a generated term may call: `leading` anywhere, and `guarded` after a non-empty literal. */
  private final case class Calls(leading: Vector[Int], guarded: Vector[Int])

  /** Random grammars of the given depth.
    *
    * With `layered`, rule *i* of a family begins with a call of rule *j* only for *j* > *i*, and calls any rule after
    * a non-empty literal, so a family has no left recursion. Without it, a rule calls any rule anywhere, and a
    * recursive rule may call itself after a prefix that consumes nothing.
    */
  private def node(depth: Int, calls: Calls, layered: Boolean): Gen[Term] = {
    val call: List[(Int, Gen[Term])] = {
      if calls.leading.isEmpty then Nil else List(3 -> Gen.oneOf(calls.leading).map(Call(_)))
    }
    val leaf: Gen[Term] = Gen.frequency(
      (List[(Int, Gen[Term])](
        2 -> Gen.oneOf("a", "b", "ab", "(", "").map(Lit(_)),
        2 -> Gen.oneOf("a+", "[ab]", "b*", "\\(", "^a", "(?<=a)b").map(Re(_)),
        2 -> Gen.choose(-3, 3).map(Arith(_)),
        2 -> Gen.const(Fail),
      ) ++ call)*
    )

    if depth <= 0 then leaf
    else {
      val sub                      = node(depth - 1, calls, layered)
      val silent: Gen[Term]        = Gen.oneOf(sub.map(Look(_)), sub.map(Neg(_)), Gen.const(Lit("")), Gen.const(Arith(1)))
      val after: Gen[Term]         = node(depth - 1, Calls(calls.guarded, calls.guarded), layered)
      def family(n: Int): Gen[Term] = {
        val all = Vector.range(0, n)
        Gen
          .sequence[Vector[Term], Term](all.map { i =>
            node(depth - 1, Calls(if layered then all.drop(i + 1) else all, all), layered)
          })
          .map(Family(_))
      }
      val guarded: List[(Int, Gen[Term])] = {
        if calls.guarded.isEmpty then Nil
        else List(3 -> Gen.zip(Gen.oneOf("a", "b", "("), after).map((s, q) => Then(Lit(s), q)))
      }
      val unguarded: List[(Int, Gen[Term])] = {
        if layered then Nil else List(2 -> Gen.zip(sub, silent).map(Unguarded(_, _)))
      }
      Gen.frequency(
        (List[(Int, Gen[Term])](
          3 -> leaf,
          2 -> Gen.zip(sub, sub).map(Then(_, _)),
          2 -> Gen.zip(sub, sub).map(Alt(_, _)),
          1 -> sub.map(Look(_)),
          1 -> sub.map(Neg(_)),
          1 -> Gen.zip(sub, sub).map(Both(_, _)),
          1 -> Gen.zip(sub, Gen.choose(-3, 3)).map(Try(_, _)),
          1 -> sub.map(Many(_)),
          1 -> Gen.zip(sub, Gen.choose(0, 2)).map(Exactly(_, _)),
          1 -> Gen.zip(sub, Gen.choose(0, 2)).map(AtLeast(_, _)),
          1 -> Gen.zip(sub, sub).map(SepBy(_, _)),
          1 -> sub.map(Loop(_)),
          1 -> Gen.zip(sub, Gen.oneOf("(", "a"), Gen.oneOf(")", "b")).map(Nest(_, _, _)),
          1 -> Gen.zip(Gen.oneOf("x", "y"), sub).map(Named(_, _)),
          1 -> Gen.zip(sub, sub).map(Zipped(_, _)),
          1 -> Gen.zip(sub, sub).map(Branched(_, _)),
          1 -> Gen.zip(sub, sub).map(Tagged(_, _)),
          1 -> Gen.zip(sub, Gen.choose(-3, 3)).map(Opt(_, _)),
          1 -> Gen.zip(sub, Gen.choose(-3, 3)).map(Maybe(_, _)),
          1 -> sub.map(Many1(_)),
          1 -> Gen.zip(sub, sub, sub).map(Between(_, _, _)),
          1 -> Gen.zip(sub, Gen.choose(-3, 3)).map(Pre(_, _)),
          2 -> Gen.choose(2, 3).flatMap(family),
        ) ++ guarded ++ unguarded)*
      )
    }
  }

  /** Random grammars without left recursion: a recursive rule consumes its opening text before it calls itself, and
    * the families of rules are layered, i.e. rule *i* begins with a call of rule *j* only for *j* > *i*, and calls any
    * rule after a non-empty literal.
    */
  val terms: Gen[Term] = {
    Gen.choose(0, 3).flatMap(node(_, Calls(Vector.empty, Vector.empty), layered = true))
  }

  /** Random grammars with unguarded recursion: [[terms]], rules that call themselves after a prefix that consumes
    * nothing, and families in which every rule may begin with a call of every rule.
    */
  val unguardedTerms: Gen[Term] = {
    Gen.choose(0, 3).flatMap(node(_, Calls(Vector.empty, Vector.empty), layered = false))
  }

  /** Short sources over the alphabet of the generated grammars. */
  val sources: Gen[String] = {
    Gen.choose(0, 6).flatMap(n => Gen.listOfN(n, Gen.oneOf('a', 'b', '(', ')')).map(_.mkString))
  }

  /** Positions in sources: what remains to be read is a sample of [[sources]], after a prefix that is also one. */
  val inputs: Gen[ReferenceParser.Input] = {
    Gen.zip(sources, sources).map((prefix, rest) => ReferenceParser.Input(prefix + rest, prefix.length))
  }
}

/** The interpreters under test, as stable values. */
object Interpreters {
  val reference: ReferenceParser = ReferenceParser()
  val strict: StrictParser       = StrictParser()
}

/** The morphisms of [[Fns]]: lifted functions, observed by application. */
object FnsFixture extends CategoryFixture("Fn", Fns) {

  def arrow[X: Sample, Y: Sample]: Gen[Fn[X, Y]] = Sample.function[X, Y].map(Fn.lift(_))

  def variant[X: Sample, Y: Sample](f: Fn[X, Y]): Fn[X, Y] = Fn.Compose(f, Fn.Id())

  def observe[X: Sample, Y: Sample]: Gen[Fn[X, Y] is Observable] = {
    Sample.points[X].map { points =>
      Observable.through[Fn[X, Y], Y](points.map(x => (f: Fn[X, Y]) => f(x)))(using
        Observable.EqIsObservable(using Y.eq)
      )
    }
  }
}

/** Generated parsers of an interpreter: a random grammar between random pure functions, observed by running on sample
  * semantic inputs at sample positions in sources.
  */
object ParserGen {

  /** Parsers *X* → *Y*: *X* is hashed to an integer, a random grammar runs, and its result is mapped to *Y*. */
  def arrow[X: Sample, Y: Sample](alg: ParserAlgebra): Gen[alg.P[X, Y]] = {
    import alg.*
    for {
      term <- Grammars.terms
      in   <- Sample.function[X, Int]
      out  <- Sample.function[Int, Y]
    } yield pure(lift(in)) >> Grammars.interpret(alg)(term) >> pure(lift(out))
  }

  /** Sample semantic inputs and positions in sources, at which parsers are observed. */
  private def points[X: Sample]: Gen[List[(X, ReferenceParser.Input)]] = {
    Gen.listOfN(6, Gen.zip(X.gen, Grammars.inputs))
  }

  /** Observations of parsers *X* → *Y* including diagnostics: what they report, their results and offsets. */
  def exact[X: Sample, Y: Sample](semantics: Semantics): Gen[semantics.algebra.P[X, Y] is Observable] = {
    points[X].map(points => exactAt[X, Y](semantics)(points))
  }

  /** The order of parsers *X* → *Y*: the same results and offsets, and at least as much diagnostics. */
  def order[X: Sample, Y: Sample](semantics: Semantics): Gen[semantics.algebra.P[X, Y] is Preorder] = {
    points[X].map(points => orderAt[X, Y](semantics)(points))
  }

  /** [[exact]] and [[order]] at the same sample points, for the laws that relate them. */
  def oracles[X: Sample, Y: Sample](
    semantics: Semantics
  ): Gen[(semantics.algebra.P[X, Y] is Observable, semantics.algebra.P[X, Y] is Preorder)] = {
    points[X].map(points => (exactAt[X, Y](semantics)(points), orderAt[X, Y](semantics)(points)))
  }

  /** [[exact]] at the given sample points. */
  private def exactAt[X, Y: Sample](semantics: Semantics)(
    points: List[(X, ReferenceParser.Input)]
  ): semantics.algebra.P[X, Y] is Observable = {
    Observable.through[semantics.algebra.P[X, Y], (Expected, Option[(Y, Int)])](points.map((x, in) =>
      p => semantics.diagnose(p)(x, in.source, in.offset)
    ))(
      using
      Observable.EqIsObservable(
        using Eq.Tuple2IsEq(using Expected.ExpectedIsEq, Eq.OptionIsEq(using Eq.Tuple2IsEq(using Y.eq, Eq.IntIsEq)))
      )
    )
  }

  /** [[order]] at the given sample points. */
  private def orderAt[X, Y: Sample](semantics: Semantics)(
    points: List[(X, ReferenceParser.Input)]
  ): semantics.algebra.P[X, Y] is Preorder = {
    val outcomes: (Expected, Option[(Y, Int)]) is Preorder = new Preorder {
      type Self = (Expected, Option[(Y, Int)])

      def below(a: Self, b: Self): Boolean = {
        Expected.ExpectedIsPreorder.below(a._1, b._1) &&
        Eq.OptionIsEq(using Eq.Tuple2IsEq(using Y.eq, Eq.IntIsEq)).equal(a._2, b._2)
      }
    }
    Preorder.through[semantics.algebra.P[X, Y], (Expected, Option[(Y, Int)])](points.map((x, in) =>
      p => semantics.diagnose(p)(x, in.source, in.offset)
    ))(
      using outcomes
    )
  }

  /** A parser equal to *p* by construction, diagnostics included: *p* then the identity, which reports nothing. */
  def variant[X, Y](alg: ParserAlgebra)(p: alg.P[X, Y]): alg.P[X, Y] = {
    import alg.*
    p >> pure(lift[Y, Y](y => y))
  }

  /** A parser that reports at least as much as *p*: where *p* fails, *q* also runs and fails. */
  def refine[X, Y](alg: ParserAlgebra)(p: alg.P[X, Y], q: alg.P[X, Y]): alg.P[X, Y] = {
    import alg.*
    p |> (q >> failure[Y, Y])
  }

  /** Diagnostics at a few positions, over a few labels and rules, nothing reported included. */
  val expected: Gen[Expected] = {
    val expectation = Gen.zip(Gen.oneOf("a", "b", "c"), Gen.oneOf(Nil, List("r"), List("r", "s")))
    Gen.frequency(
      1 -> Gen.const(Expected.bottom),
      4 -> Gen.zip(Gen.choose(0, 3), Gen.containerOf[Set, (String, List[String])](expectation)).map((n, labels) =>
        Expected(n, labels.map(Expectation(_, _)))
      ),
    )
  }

  /** Observations of parsers *X* → *Y*: their results and offsets at sample semantic inputs and positions in sources.
    */
  def observe[X: Sample, Y: Sample](semantics: Semantics): Gen[semantics.algebra.P[X, Y] is Observable] = {
    points[X].map { points =>
      Observable.through[semantics.algebra.P[X, Y], Option[(Y, Int)]](points.map((x, in) =>
        p => semantics.run(p)(x, in.source, in.offset)
      ))(
        using Observable.EqIsObservable(using Eq.OptionIsEq(using Eq.Tuple2IsEq(using Y.eq, Eq.IntIsEq)))
      )
    }
  }
}

object ReferenceFixture extends PromonadFixture("ReferenceParser", Interpreters.reference.sequencing) {
  import promonad.P
  val category: TotalFixture.type = TotalFixture

  def arrow[X: Sample, Y: Sample]: Gen[P[X, Y]] = ParserGen.arrow[X, Y](Interpreters.reference)

  def variant[X: Sample, Y: Sample](p: P[X, Y]): P[X, Y] =
    Interpreters.reference.orElse(p, Interpreters.reference.failure)

  def observe[X: Sample, Y: Sample]: Gen[P[X, Y] is Observable] = {
    ParserGen.observe[X, Y](Interpreters.reference.Semantics)
  }
}

object StrictFixture extends PromonadFixture("StrictParser", Interpreters.strict.sequencing) {
  import promonad.P
  val category: FnsFixture.type = FnsFixture

  def arrow[X: Sample, Y: Sample]: Gen[P[X, Y]] = ParserGen.arrow[X, Y](Interpreters.strict)

  def variant[X: Sample, Y: Sample](p: P[X, Y]): P[X, Y] = Interpreters.strict.rule(p, "variant")

  def observe[X: Sample, Y: Sample]: Gen[P[X, Y] is Observable] = {
    ParserGen.observe[X, Y](Interpreters.strict.Semantics)
  }
}

/** [[ReferenceFixture]], observed with diagnostics and varied by an identity that reports nothing. */
object ReferenceDiagnosticsFixture
    extends CategoryFixture("ReferenceParser (with diagnostics)", ReferenceFixture.promonad.arrows) {
  import category.-->

  def arrow[X: Sample, Y: Sample]: Gen[X --> Y] = ReferenceFixture.arrow[X, Y]

  def variant[X: Sample, Y: Sample](p: X --> Y): X --> Y = ParserGen.variant(Interpreters.reference)(p)

  def observe[X: Sample, Y: Sample]: Gen[(X --> Y) is Observable] = {
    ParserGen.exact[X, Y](Interpreters.reference.Semantics)
  }
}

/** [[StrictFixture]], observed with diagnostics and varied by an identity that reports nothing. */
object StrictDiagnosticsFixture
    extends CategoryFixture("StrictParser (with diagnostics)", StrictFixture.promonad.arrows) {
  import category.-->

  def arrow[X: Sample, Y: Sample]: Gen[X --> Y] = StrictFixture.arrow[X, Y]

  def variant[X: Sample, Y: Sample](p: X --> Y): X --> Y = ParserGen.variant(Interpreters.strict)(p)

  def observe[X: Sample, Y: Sample]: Gen[(X --> Y) is Observable] = {
    ParserGen.exact[X, Y](Interpreters.strict.Semantics)
  }
}

/** The fixtures of the interpreters.
  *
  * A spec finds the fixture of the promonad or category it checks among these givens, so there is one per promonad
  * and one per category.
  */
object ParserFixtures {

  /** [[ReferenceFixture]], for the promonad of `ReferenceParser`. */
  given ReferenceIsFixture: PromonadFixture.For[Interpreters.reference.sequencing.type] = ReferenceFixture

  /** [[ReferenceFixture]], for the category of `ReferenceParser`. */
  given ReferenceCategoryIsFixture: CategoryFixture.For[Interpreters.reference.sequencing.arrows.type] = {
    ReferenceFixture.arrows
  }

  /** [[StrictFixture]], for the promonad of `StrictParser`. */
  given StrictIsFixture: PromonadFixture.For[Interpreters.strict.sequencing.type] = StrictFixture

  /** [[StrictFixture]], for the category of `StrictParser`. */
  given StrictCategoryIsFixture: CategoryFixture.For[Interpreters.strict.sequencing.arrows.type] = StrictFixture.arrows

  /** [[FnsFixture]], for the pure functions of `StrictParser`. */
  given FnsIsFixture: CategoryFixture.For[Fns.type] = FnsFixture
}
