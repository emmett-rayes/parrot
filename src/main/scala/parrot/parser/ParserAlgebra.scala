package parrot
package parser

import category.*

import scala.annotation.targetName
import scala.util.Try
import scala.util.matching.Regex

/** An algebra of parsers: the combinators of parsing expression grammars, derived from categorical structure.
  *
  * A parser *P*(*A*,*B*) consumes a prefix of the input while turning a semantic input *A* into a semantic result *B*.
  * No combinator is primitive except those that read the input. Each of the others is an operation of one of the
  * structures the algebra is built from, where
  *   - [[Arrows]]: parsers form a promonad over the category of pure functions (*unit*, ⨾)
  *   - [[Products]] and [[Coproducts]]: pairs and tagged unions of semantic values, in the category of pure functions
  *   - [[Zipping]]: a strength over products, which makes parsers a Freyd category (⋉, ⟨-,-⟩)
  *   - [[Branching]]: a strength over coproducts (+, [-,-])
  *   - [[Choice]]: a classical restriction structure (0, *p̄*, *p̄*ᶜ, *attempt*, ⊳)
  *   - [[Loops]]: guarded iteration (†, and the repetition combinators derived from it)
  *   - [[Knots]]: guarded recursion at the types of parsers (*fix*)
  *
  * Iteration and recursion are guarded by the input: a loop step that continues, or a recursive call, must come after
  * input has been consumed; otherwise that step or call fails. So every parser terminates.
  *
  * Parsers report diagnostics: what they expected where they failed furthest ([[Expected]]), a writer effect produced
  * on success and on failure. Lookahead and negation are silent: they report nothing about the parser they test.
  *
  * An interpreter chooses the structures and implements the primitives `lift`, `literal`, `regex`, `rule` and
  * `diagnose`. It may override a derived combinator with a faster implementation of the same equation.
  */
abstract class ParserAlgebra(
  tracked val Arrows: Promonad { val K: Category { type Obj = Type } },
  tracked val Products: Cartesian {
    val K: Arrows.K.type; val U: Unit is Type; val T: Bifunctor { type Self = Tuple2 }
  },
  tracked val Coproducts: Cocartesian {
    val K: Arrows.K.type; val U: Nothing is Type; val T: Bifunctor { type Self = Either }
  },
  tracked val Zipping: Strong { val P: Arrows.type; val M: Products.type },
  tracked val Branching: Strong { val P: Arrows.type; val M: Coproducts.type },
  tracked val Choice: Classical { val P: Arrows.type; val C: Coproducts.type },
  tracked val Loops: Elgot { val S: Branching.type },
  tracked val Knots: Recursion { val P: Arrows.type },
) extends caps.Pure {
  import Arrows.K.>>>

  /** Parsers *P*(*A*,*B*) from semantic input *A* to semantic result *B*. */
  final type P = Arrows.P

  /** Pure functions on semantic values. */
  final type --> = Arrows.K.-->

  // ==== Primitives ====

  /** Includes a pure Scala function among the pure functions of the algebra. */
  def lift[A, B](f: A -> B): A --> B

  /** Names `p` as the rule `label`, for diagnostics. It runs `p`; where `p` fails at or before its start, it reports
    * that it expected `label` there, and otherwise it puts every expectation of `p` in the context of `label`.
    */
  def rule[A, B](p: P[A, B], label: String): P[A, B]

  /** Consumes `expected`. */
  def literal(expected: String): P[Unit, String]

  /** Consumes a match of `expected`, taken in context: `^` and `$` match only at the start and end of the whole input,
    * and lookbehind and `\b` see the input before the current position.
    */
  def regex(expected: Regex): P[Unit, String]

  /** Runs `p` on semantic input `a` at the start of `source`: what it expected where it failed furthest, and its result
    * and the offset after it, if it succeeds.
    */
  def diagnose[A, B](p: P[A, B])(a: A, source: String): (Expected, Option[(B, Int)])

  /** Runs `p` on semantic input `a` at the start of `source`: its result and the offset after it, if it succeeds. */
  def run[A, B](p: P[A, B])(a: A, source: String): Option[(B, Int)] = {
    diagnose(p)(a, source)._2
  }

  extension [B](p: P[Unit, B]) {

    /** Runs `p` on a prefix of `source`, reporting what was expected where it failed furthest if it fails. */
    def parse(source: String): Try[(result: B, offset: Int)] = {
      diagnose(p)((), source) match {
        case (_, Some((result, offset))) => scala.util.Success((result = result, offset = offset))
        case (expected, scala.None)      => scala.util.Failure(ParseError(expected))
      }
    }

    /** Runs `p` on the whole of `source`. */
    def parseAll(source: String): Try[(result: B, offset: Int)] = {
      diagnose(p)((), source) match {
        case (_, Some((result, offset))) if offset == source.length =>
          scala.util.Success((result = result, offset = offset))
        case (expected, Some((_, offset))) =>
          scala.util.Failure(ParseError(expected.join(Expected.at(offset, "end of input"))))
        case (expected, scala.None) => scala.util.Failure(ParseError(expected))
      }
    }
  }

  // ==== Sequencing: the promonad ====

  /** From the promonad: *unit*(*f*) applies *f* to the semantic input without consuming anything, and the identity
    * arrow *id* succeeds without consuming anything, returning its semantic input.
    */
  export Arrows.{identity as success, unit as pure}

  /** Runs *p*, then *q* on the remaining input with the result of *p* as its semantic input: *p* ⨾ *q*. */
  def andThen[A, B, C](p: P[A, B], q: P[B, C]): P[A, C] = {
    Arrows.multiply(q, p)
  }

  /** Applies *g* to the result of *p*: *p* ⨾ *unit*(*g*). */
  def map[A, B, C](p: P[A, B], g: B --> C): P[A, C] = {
    andThen(p, pure(g))
  }

  /** Applies *f* to the semantic input before passing it to *p*: *unit*(*f*) ⨾ *p*. */
  def mapInput[A, B, C](p: P[A, B], f: C --> A): P[C, B] = {
    andThen(pure(f), p)
  }

  // ==== Zipping and branching: the strengths ====

  /** Runs *p* on the left of a pair of semantic inputs, then *q* on the right: *p* ⋉ *q* = *first*(*p*) ⨾ *second*(*q*).
    */
  def zip[A, B, C, D](p: P[A, B], q: P[C, D]): P[(A, C), (B, D)] = {
    andThen(Zipping.first[A, B, C](p), Zipping.second[C, D, B](q))
  }

  /** Runs *p* on a left semantic input or *q* on a right one, tagging the result: *p* + *q*. */
  def branch[A, B, C, D](p: P[A, B], q: P[C, D]): P[Either[A, C], Either[B, D]] = {
    andThen(Branching.first[A, B, C](p), Branching.second[C, D, B](q))
  }

  /** Runs *p* on a left semantic input or *q* on a right one, into a common result: [*p*,*q*]. */
  def merge[A, B, C](p: P[A, C], q: P[B, C]): P[Either[A, B], C] = {
    map(branch(p, q), Coproducts.codiagonal[C])
  }

  // ==== Choice: the classical restriction structure ====

  /** From the classical restriction structure:
    *   - 0 fails without consuming anything: the restriction zero
    *   - *p̄* succeeds if and only if *p* succeeds, consuming nothing and returning the semantic input: lookahead
    *   - *p̄*ᶜ succeeds if and only if *p* fails, consuming nothing and returning the semantic input: negation
    *   - *attempt*(*p*) never fails: the result of *p* on the left, or the untouched semantic input on the right where
    *     *p* fails
    *   - *p* ⊳ *q* tries *p* and, only where it fails, *q* on the original input: override, PEG ordered choice
    */
  export Choice.{attempt, attempt as optional, complement as not, orElse, restrict as lookahead, zero as failure}

  /** Ordered choice that tags the alternative that succeeded: (*p* ⨾ *ι*₁) ⊳ (*q* ⨾ *ι*₂). */
  def or[A, B, C](p: P[A, B], q: P[A, C]): P[A, Either[B, C]] = {
    orElse(map(p, Coproducts.inl[B, C]), map(q, Coproducts.inr[B, C]))
  }

  // ==== Iteration and recursion ====

  /** Runs *p* repeatedly, feeding each right result back as the next semantic input, until it yields a left result:
    * *p*†. A step that yields a right result without consuming input fails the whole loop.
    */
  def iterate[A, B](p: P[A, Either[B, A]]): P[A, B] = {
    Loops.iterate[B, A](p)
  }

  /** The parser *fix*(*f*) defined recursively by *f*, which receives the parser being defined. A recursive call that
    * is not preceded by consumed input fails.
    */
  def recursive[A, B](f: P[A, B] -> P[A, B]): P[A, B] = {
    Knots.fix(f)
  }

  /** A tuple of mutually recursive parsers: *f* receives the tuple being defined and returns its definition. Each
    * component is a knot of [[Knots]]' family fixed point, so a call that is not preceded by consumed input fails, and
    * *f* is applied once per application of the family. The tuple may contain only parsers.
    */
  inline def recursive[T <: Tuple](f: T -> T)(using Parsers[T]): T = {
    val n      = compiletime.constValue[Tuple.Size[T]]
    val family = Knots.fixFamily[Any, Any](n) { knots =>
      lazy val solved: T =
        f(Tuple.fromArray(Array.tabulate[Object](n)(i => knots(i).asInstanceOf[Object])).asInstanceOf[T])
      i => solved.productElement(i).asInstanceOf[P[Any, Any]]
    }
    Tuple.fromArray(Array.tabulate[Object](n)(i => family(i).asInstanceOf[Object])).asInstanceOf[T]
  }

  /** Evidence that every component of the tuple type `T` is a parser type `P[A, B]`. */
  final class Parsers[T <: Tuple] private[ParserAlgebra] ()

  object Parsers {

    /** The empty tuple has no other components. */
    given EmptyIsParsers: Parsers[EmptyTuple] = Parsers()

    /** A parser followed by parsers. */
    given ConsIsParsers: [A, B, Rest <: Tuple] => Parsers[Rest] => Parsers[P[A, B] *: Rest] = Parsers()
  }

  // ==== Concatenation: derived from the products of `-->` ====

  /** Runs *p*, then *q*, on the same semantic input, pairing their results: ⟨*p*,*q*⟩ = Δ ⨾ (*p* ⋉ *q*). */
  def pair[A, B, C](p: P[A, B], q: P[A, C]): P[A, (B, C)] = {
    mapInput(zip(p, q), Products.diagonal[A])
  }

  /** Runs *p*, then *q*, keeping only the result of *q*: ⟨*p*,*q*⟩ ⨾ *π*₂. */
  def skipThen[A, B, C](p: P[A, B], q: P[A, C]): P[A, C] = {
    map(pair(p, q), Products.snd[B, C])
  }

  /** Runs *p*, then *q*, keeping only the result of *p*: ⟨*p*,*q*⟩ ⨾ *π*₁. */
  def thenSkip[A, B, C](p: P[A, B], q: P[A, C]): P[A, B] = {
    map(pair(p, q), Products.fst[B, C])
  }

  /** Runs *open*, *p*, then *close*, keeping the result of *p*. */
  def between[A, B, C, D](p: P[A, B], open: P[A, C], close: P[A, D]): P[A, B] = {
    thenSkip(skipThen(open, p), close)
  }

  // ==== Repetition: derived from iteration ====

  /** Pairs the semantic input with the empty collection. */
  private def start[A, B]: P[A, (A, Vector[B])] = {
    pure(Products.pair(Arrows.K.identity[A], lift[A, Vector[B]](_ => Vector.empty)))
  }

  /** Runs *item* once on the semantic input, appending its result to the collection. */
  private def step[A, B](item: P[A, B]): P[(A, Vector[B]), (A, Vector[B])] = {
    val reshape =
      Products.pair(Products.fst[A, Vector[B]], Products.pair(Products.snd[A, Vector[B]], Products.fst[A, Vector[B]]))
    val finish = Products.tensor(Arrows.K.identity[A], lift[(Vector[B], B), Vector[B]]((bs, b) => bs :+ b))
    map(mapInput(zip(success[A], zip(success[Vector[B]], item)), reshape), finish)
  }

  /** Runs *seed*, then *item* until it fails, collecting the results. */
  private def repeat[A, B](seed: P[A, (A, Vector[B])], item: P[A, B]): P[A, Vector[B]] = {
    val next = map(step(item), Coproducts.inr[Vector[B], (A, Vector[B])])
    val done = pure(Products.snd[A, Vector[B]] >>> Coproducts.inl[Vector[B], (A, Vector[B])])
    andThen(seed, iterate(orElse(next, done)))
  }

  /** Runs *item* exactly *n* times. */
  private def unrolled[A, B](item: P[A, B], n: Int): P[A, (A, Vector[B])] = {
    require(n >= 0, "n must be non-negative")
    (0 until n).foldLeft(start[A, B])((acc, _) => andThen(acc, step(item)))
  }

  /** Runs *p* until it fails, collecting the results: *p*\*. If *p* succeeds without consuming input, the repetition
    * fails.
    */
  def repeated[A, B](p: P[A, B]): P[A, Vector[B]] = {
    repeat(start[A, B], p)
  }

  /** Runs *p* exactly *n* times, collecting the results. */
  def times[A, B](p: P[A, B], n: Int): P[A, Vector[B]] = {
    map(unrolled(p, n), Products.snd[A, Vector[B]])
  }

  /** Runs *p* at least *n* times, until it fails, collecting the results. */
  def atLeast[A, B](p: P[A, B], n: Int): P[A, Vector[B]] = {
    repeat(unrolled(p, n), p)
  }

  /** Runs *p* one or more times, separated by *separator*, collecting the results. */
  def separatedBy[A, B, C](p: P[A, B], separator: P[A, C]): P[A, Vector[B]] = {
    repeat(unrolled(p, 1), skipThen(separator, p))
  }

  // ==== Syntax ====

  extension [A, B](self: P[A, B]) {

    /** Infix form of [[rule]]. */
    @targetName("ruleExt")
    final def rule(label: String): P[A, B] = ParserAlgebra.this.rule(self, label)

    /** Infix form of [[map]]. */
    @targetName("mapExt")
    final def map[C](g: B --> C): P[A, C] = ParserAlgebra.this.map(self, g)

    /** Infix form of [[mapInput]]. */
    @targetName("mapInputExt")
    final def mapInput[C](f: C --> A): P[C, B] = ParserAlgebra.this.mapInput(self, f)

    /** Infix form of [[andThen]]. */
    final def >>[C](other: P[B, C]): P[A, C] = ParserAlgebra.this.andThen(self, other)

    /** Infix form of [[zip]]. */
    final def **[C, D](other: P[C, D]): P[(A, C), (B, D)] = ParserAlgebra.this.zip(self, other)

    /** Infix form of [[pair]]. */
    final def &&[C](other: P[A, C]): P[A, (B, C)] = ParserAlgebra.this.pair(self, other)

    /** Infix form of [[skipThen]]. */
    final def *>[C](other: P[A, C]): P[A, C] = ParserAlgebra.this.skipThen(self, other)

    /** Infix form of [[thenSkip]]. */
    final def <*[C](other: P[A, C]): P[A, B] = ParserAlgebra.this.thenSkip(self, other)

    /** Infix form of [[between]]. */
    @targetName("betweenExt")
    final def between[C, D](open: P[A, C], close: P[A, D]): P[A, B] = ParserAlgebra.this.between(self, open, close)

    /** Infix form of [[branch]]. */
    final def ++[C, D](other: P[C, D]): P[Either[A, C], Either[B, D]] = ParserAlgebra.this.branch(self, other)

    /** Infix form of [[merge]]. */
    final def ||[C](other: P[C, B]): P[Either[A, C], B] = ParserAlgebra.this.merge(self, other)

    /** Infix form of [[orElse]]. */
    final def |>(other: P[A, B]): P[A, B] = ParserAlgebra.this.orElse(self, other)

    /** Infix form of [[or]]. */
    final def +>[C](other: P[A, C]): P[A, Either[B, C]] = ParserAlgebra.this.or(self, other)

    /** Prefix form of [[lookahead]]. */
    final def unary_~ : P[A, A] = ParserAlgebra.this.lookahead(self)

    /** Prefix form of [[not]]. */
    final def unary_! : P[A, A] = ParserAlgebra.this.not(self)

    /** Postfix form of [[attempt]]. */
    @targetName("attemptExt")
    final def attempt(using DummyImplicit): P[A, Either[B, A]] = ParserAlgebra.this.attempt(self)

    /** Postfix form of [[optional]]. */
    @targetName("optionalExt")
    final def optional(using DummyImplicit): P[A, Either[B, A]] = ParserAlgebra.this.optional(self)

    /** Postfix form of [[repeated]]. */
    @targetName("repeatedExt")
    final def repeated(using DummyImplicit): P[A, Vector[B]] = ParserAlgebra.this.repeated(self)

    /** Infix form of [[times]]. */
    @targetName("timesExt")
    final def times(n: Int): P[A, Vector[B]] = ParserAlgebra.this.times(self, n)

    /** Infix form of [[atLeast]]. */
    @targetName("atLeastExt")
    final def atLeast(n: Int): P[A, Vector[B]] = ParserAlgebra.this.atLeast(self, n)

    /** Infix form of [[separatedBy]]. */
    @targetName("separatedByExt")
    final def separatedBy[C](separator: P[A, C]): P[A, Vector[B]] = ParserAlgebra.this.separatedBy(self, separator)
  }

  extension [A, B](self: P[A, Either[B, A]])
    /** Postfix form of [[iterate]]. */
    @targetName("iterateExt")
    final def iterate(using DummyImplicit): P[A, B] = ParserAlgebra.this.iterate(self)

  /** The equations of parsing expression grammars, in the vocabulary of parsers. Most are laws of the structures the
    * algebra is built from; checking them on the combinators also checks the overrides of interpreters.
    *
    * The laws come in two tiers. Equations hold for results, offsets and diagnostics, observed with an [[Observable]].
    * Inequations *p* ⊑ *q* say that *p* and *q* have the same results and offsets and that *q* reports at least what
    * *p* reports, observed with a [[Preorder]]: they are the equations that only hold up to diagnostics, because a
    * silent lookahead or a failure forgets what the parser before it expected. Every combinator preserves ⊑, so parsers
    * are enriched over preorders.
    */
  object ParserLaws {

    /** *id* ⨾ *p* = *p* */
    def leftIdentity[A, B](p: P[A, B])(using P[A, B] is Observable): Boolean = {
      (success[A] >> p) =?= p
    }

    /** *p* ⨾ *id* = *p* */
    def rightIdentity[A, B](p: P[A, B])(using P[A, B] is Observable): Boolean = {
      (p >> success[B]) =?= p
    }

    /** (*p* ⨾ *q*) ⨾ *r* = *p* ⨾ (*q* ⨾ *r*) */
    def associativity[A, B, C, D](p: P[A, B], q: P[B, C], r: P[C, D])(using P[A, D] is Observable): Boolean = {
      ((p >> q) >> r) =?= (p >> (q >> r))
    }

    /** *id* ⋉ *id* = *id* */
    def zipIdentity[A, C](using P[(A, C), (A, C)] is Observable): Boolean = {
      (success[A] ** success[C]) =?= success[(A, C)]
    }

    /** 0 ⨾ *p* = 0: nothing runs after a failure. */
    def leftZero[A, B, C](p: P[B, C])(using P[A, C] is Observable): Boolean = {
      (failure[A, B] >> p) =?= failure[A, C]
    }

    /** 0 ⊑ *p* ⨾ 0: a failure at the end fails the whole sequence, which still reports what *p* expected.
      */
    def rightZero[A, B, C](p: P[A, B])(using P[A, C] is Preorder): Boolean = {
      failure[A, C] <~ (p >> failure[B, C])
    }

    /** 0 ⊳ *p* = *p* = *p* ⊳ 0 */
    def choiceIdentity[A, B](p: P[A, B])(using P[A, B] is Observable): Boolean = {
      ((failure[A, B] |> p) =?= p) && ((p |> failure[A, B]) =?= p)
    }

    /** (*p* ⊳ *q*) ⊳ *r* = *p* ⊳ (*q* ⊳ *r*) */
    def choiceAssociativity[A, B](p: P[A, B], q: P[A, B], r: P[A, B])(using P[A, B] is Observable): Boolean = {
      ((p |> q) |> r) =?= (p |> (q |> r))
    }

    /** *h* ⨾ (*p* ⊳ *q*) = (*h* ⨾ *p*) ⊳ (*h* ⨾ *q*): choice distributes over what comes before it. */
    def choicePrecomposition[A, B, C](h: P[A, B], p: P[B, C], q: P[B, C])(using P[A, C] is Observable): Boolean = {
      (h >> (p |> q)) =?= ((h >> p) |> (h >> q))
    }

    /** *p* ⊳ *q* = *attempt*(*p*) ⨾ [*id*,*q*]: ordered choice is an attempt followed by a merge. */
    def choiceByAttempt[A, B](p: P[A, B], q: P[A, B])(using P[A, B] is Observable): Boolean = {
      (p |> q) =?= (attempt(p) >> (success[B] || q))
    }

    /** *p̄* ⨾ *p* ⊑ *p* (**R1**, up to diagnostics): where *p* fails, the silent lookahead reports nothing. */
    def lookaheadIdentity[A, B](p: P[A, B])(using P[A, B] is Preorder): Boolean = {
      (~p >> p) <~ p
    }

    /** *p̄* ⨾ *q̄* = *q̄* ⨾ *p̄* (**R2**) */
    def lookaheadCommutativity[A, B, C](p: P[A, B], q: P[A, C])(using P[A, A] is Observable): Boolean = {
      (~p >> ~q) =?= (~q >> ~p)
    }

    /** (*p̄* ⨾ *q*)‾ = *p̄* ⨾ *q̄* (**R3**) */
    def lookaheadCompose[A, B, C](p: P[A, B], q: P[A, C])(using P[A, A] is Observable): Boolean = {
      ~(~p >> q) =?= (~p >> ~q)
    }

    /** (*p* ⨾ *q*)‾ ⨾ *p* ⊑ *p* ⨾ *q̄* (**R4**, up to diagnostics): on the left, *p* runs only inside the silent
      * lookahead when *q* fails.
      */
    def lookaheadPrecompose[A, B, C](p: P[A, B], q: P[B, C])(using P[A, B] is Preorder): Boolean = {
      (~(p >> q) >> p) <~ (p >> ~q)
    }

    /** (*p̄*ᶜ)ᶜ = *p̄* */
    def doubleNegation[A, B](p: P[A, B])(using P[A, A] is Observable): Boolean = {
      !(!p) =?= ~p
    }

    /** *p̄* ⨾ *p̄*ᶜ = 0: a parser cannot both succeed and fail. */
    def negationExclusion[A, B](p: P[A, B])(using P[A, A] is Observable): Boolean = {
      (~p >> !p) =?= failure[A, A]
    }

    /** *p̄* ⊳ *p̄*ᶜ = *id*: a parser either succeeds or fails. */
    def negationCover[A, B](p: P[A, B])(using P[A, A] is Observable): Boolean = {
      (~p |> !p) =?= success[A]
    }

    /** *p*† = *p* ⨾ [*id*,*p*†], for a guarded *p*. */
    def loopUnfolding[A, B](p: P[A, Either[B, A]])(using P[A, B] is Observable): Boolean = {
      p.iterate =?= (p >> (success[B] || p.iterate))
    }

    /** *fix*(*f*) = *f*(*fix*(*f*)), for a guarded *f*. */
    def recursionUnfolding[A, B](f: P[A, B] -> P[A, B])(using P[A, B] is Observable): Boolean = {
      recursive(f) =?= f(recursive(f))
    }

    /** *rule*(*p*,*l*) ≡ *p*: rules change diagnostics only. Observed without diagnostics. */
    def ruleTransparent[A, B](p: P[A, B], label: String)(using P[A, B] is Observable): Boolean = {
      p.rule(label) =?= p
    }

    /** If *p* ⊑ *p*′ and *q* ⊑ *q*′, then *p* ⨾ *q* ⊑ *p*′ ⨾ *q*′.
      *
      * @note The premise is not checked: *p*′ and *q*′ must be built to report more than *p* and *q*.
      */
    def andThenMonotone[A, B, C](p: P[A, B], p2: P[A, B], q: P[B, C], q2: P[B, C])(
      using P[A, C] is Preorder
    ): Boolean = {
      (p >> q) <~ (p2 >> q2)
    }

    /** If *p* ⊑ *p*′ and *q* ⊑ *q*′, then *p* ⊳ *q* ⊑ *p*′ ⊳ *q*′. */
    def orElseMonotone[A, B](p: P[A, B], p2: P[A, B], q: P[A, B], q2: P[A, B])(using P[A, B] is Preorder): Boolean = {
      (p |> q) <~ (p2 |> q2)
    }

    /** If *p* ⊑ *p*′ and *q* ⊑ *q*′, then *p* ⋉ *q* ⊑ *p*′ ⋉ *q*′. */
    def zipMonotone[A, B, C, D](p: P[A, B], p2: P[A, B], q: P[C, D], q2: P[C, D])(
      using P[(A, C), (B, D)] is Preorder
    ): Boolean = {
      (p ** q) <~ (p2 ** q2)
    }

    /** If *p* ⊑ *p*′, then *rule*(*p*,*l*) ⊑ *rule*(*p*′,*l*). */
    def ruleMonotone[A, B](p: P[A, B], p2: P[A, B], label: String)(using P[A, B] is Preorder): Boolean = {
      p.rule(label) <~ p2.rule(label)
    }

    /** *p*\* = (⟨*p*,*p*\*⟩ ⨾ *unit*(*cons*)) ⊳ *unit*(*empty*), for a *p* that consumes when it succeeds: *cons* prepends
      * a result to the collection, and *empty* is the empty collection.
      */
    def repeatedUnfolding[A, B](p: P[A, B])(using P[A, Vector[B]] is Observable): Boolean = {
      val cons  = lift[(B, Vector[B]), Vector[B]]((b, bs) => b +: bs)
      val empty = lift[A, Vector[B]](_ => Vector.empty)
      p.repeated =?= ((p && p.repeated).map(cons) |> pure(empty))
    }
  }
}

/** A parse failure, reported as what was expected where it failed furthest.
  *
  * A parse can fail without expecting anything, for instance at a failure or at a negation whose parser succeeded,
  * since those are silent. Its diagnostics are then ⊥, and it is reported as a failure at the start.
  */
final case class ParseError(expected: Expected) extends Exception with scala.util.control.NoStackTrace {

  /** The furthest position at which something failed, or the start if nothing was expected. */
  def offset: Int = expected.position.max(0)

  override def getMessage: String = {
    if expected.expectations.isEmpty then s"no parse at position $offset"
    else s"expected ${expected.describe} at position $offset"
  }
}
