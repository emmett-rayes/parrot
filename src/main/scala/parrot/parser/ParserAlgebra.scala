package parrot
package parser

import category.*

import scala.annotation.targetName
import scala.util.matching.Regex

import category.Category.Type

/** An algebra of parsers on a category of pure functions.
  *
  * Represents parsers *P*(*A*,*B*), which consume a prefix of the input while turning a semantic input *A* into a
  * semantic result *B*, where
  *   - [[sequencing]] runs one parser after another on the remaining input, and turns pure functions into parsers
  *   - [[products]] combines several results into one, as a pair
  *   - [[coproducts]] records which of two alternatives produced a result, as a tagged union
  *   - [[zipping]] runs a parser on one component of a pair, which gives concatenation
  *   - [[branching]] runs a parser on one side of a tagged union, so that the tag decides which parser runs
  *   - [[choice]] gives ordered choice with backtracking, lookahead, negation and failure
  *   - [[loops]] runs a parser repeatedly, which gives repetition
  *   - [[knots]] lets a parser refer to itself, which gives recursive rules
  *
  * An interpreter chooses the structures and implements the primitives `lift`, `literal`, `regex` and `rule`. Every
  * other combinator is derived. An interpreter may override one with a faster implementation as long as it respects
  * the same equations. See [[ParserAlgebra.ParserLaws]]. What its parsers mean, and how they are run, is its
  * [[Semantics]].
  *
  * @note Iteration and recursion are guarded by the input. A loop step that continues, or a recursive call, fails
  *   unless input was consumed before it, so every parser terminates.
  *
  * @note Diagnostics are a writer effect, produced on success and on failure. Lookahead and negation are silent with
  *   respect to diagnostics. See [[Expected]].
  */

abstract class ParserAlgebra(
  tracked val sequencing: Promonad.On[Category { type Obj = Type }],
  tracked val products: Cartesian.On[sequencing.category.type] {
    val unit: Unit is sequencing.category.Object; val tensor: Bifunctor { type Self = Tuple2 }
  },
  tracked val coproducts: Cocartesian.On[sequencing.category.type] {
    val unit: Nothing is sequencing.category.Object; val tensor: Bifunctor { type Self = Either }
  },
  tracked val zipping: Bistrong.On[sequencing.type] { val monoidal: products.type },
  tracked val branching: Bistrong.On[sequencing.type] { val monoidal: coproducts.type },
  tracked val choice: Classical.On[sequencing.arrows.type],
  tracked val loops: GuardedIteration.On[branching.type],
  tracked val knots: GuardedRecursion.On[sequencing.type],
) extends caps.Pure {
  import sequencing.category.>>>

  /** Parsers *P*(*A*,*B*) from semantic input *A* to semantic result *B*. */
  final type P = sequencing.P

  /** Pure functions on semantic values. */
  final type --> = sequencing.category.-->

  // ==== Primitives ====

  /** Includes a pure Scala function among the pure functions of the algebra. */
  def lift[A, B](f: A -> B): A --> B

  /** Names `p` as the rule `label`.
    *
    * This is used for diagnostics, where the rule parses exactly as `p` does. If `p` fails without expecting anything
    * past its start, the rule reports that it expected `label` there. Otherwise, it reports what `p` expected, with
    * `label` added to the context of each expectation.
    */
  def rule[A, B](p: P[A, B], label: String): P[A, B]

  /** Consumes `expected`. */
  def literal(expected: String): P[Unit, String]

  /** Consumes a match of `expected`, taken in context: `^` and `$` match only at the start and end of the whole input,
    * and lookbehind and `\b` see the input before the current position.
    */
  def regex(expected: Regex): P[Unit, String]

  // ==== Sequencing: the promonad ====

  /** Succeeds without consuming anything, returning its semantic input: the identity arrow *id*. */
  final def success[A]: P[A, A] = {
    sequencing.arrows.identity[A]
  }

  /** Applies *f* to the semantic input without consuming anything: *unit*(*f*). */
  final def pure[A, B](f: A --> B): P[A, B] = {
    sequencing.unit(f)
  }

  /** Runs *p*, then *q* on the remaining input with the result of *p* as its semantic input: *p* ⨾ *q*. */
  final def andThen[A, B, C](p: P[A, B], q: P[B, C]): P[A, C] = {
    sequencing.arrows.andThen(p, q)
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

  /** Parsers as a Freyd category over products, with the strength [[zipping]]. */
  final lazy val zipped: Freyd.On[zipping.type] = Freyd(zipping)

  /** Parsers as a Freyd category over coproducts, with the strength [[branching]]. */
  final lazy val branched: Freyd.On[branching.type] = Freyd(branching)

  /** Runs *p* on the left of a pair of semantic inputs, then *q* on the right: *p* ⋉ *q* in [[zipped]]. */
  def zip[A, B, C, D](p: P[A, B], q: P[C, D]): P[(A, C), (B, D)] = {
    zipped.leftToRight(p, q)
  }

  /** Runs *p* on a left semantic input or *q* on a right one, tagging the result: *p* + *q* in [[branched]]. */
  def branch[A, B, C, D](p: P[A, B], q: P[C, D]): P[Either[A, C], Either[B, D]] = {
    branched.leftToRight(p, q)
  }

  /** Runs *p* on a left semantic input or *q* on a right one, into a common result: [*p*,*q*].
    *
    * @note Where parsers are the arrows of a Kleisli promonad, this is the copairing of their coproducts
    *   ([[category.Kleisli.CocartesianOf]]).
    */
  def merge[A, B, C](p: P[A, C], q: P[B, C]): P[Either[A, B], C] = {
    map(branch(p, q), coproducts.codiagonal[C])
  }

  // ==== Choice: the classical restriction structure ====

  /** Runs *p*, or *q* on the same input where *p* fails: ordered choice, the override *p* ⊳ *q*. */
  final def orElse[A, B](p: P[A, B], q: P[A, B]): P[A, B] = {
    choice.orElse(p, q)
  }

  /** Fails without consuming anything: the restriction zero 0. */
  final def failure[A, B]: P[A, B] = {
    choice.zero[A, B]
  }

  /** Succeeds if and only if *p* succeeds, consuming nothing and returning the semantic input: the restriction *p̄*. */
  final def lookahead[A, B](p: P[A, B]): P[A, A] = {
    choice.restrict(p)
  }

  /** Succeeds if and only if *p* fails, consuming nothing and returning the semantic input: the complement *p̄*ᶜ. */
  final def not[A, B](p: P[A, B]): P[A, A] = {
    choice.complement(p)
  }

  /** Never fails: the result of *p* on the left, or the untouched semantic input on the right where *p* fails:
    * *attempt*(*p*).
    */
  final def optional[A, B](p: P[A, B]): P[A, Either[B, A]] = {
    attempt(p)
  }

  /** Tags the result of *p* on the left, or returns the untouched semantic input on the right where *p* fails:
    * *attempt*(*p*) = (*p* ⨾ *ι*₁) ⊳ *ι*₂.
    */
  def attempt[A, B](p: P[A, B]): P[A, Either[B, A]] = {
    orElse(map(p, coproducts.inl[B, A]), pure(coproducts.inr[B, A]))
  }

  /** Ordered choice that tags the alternative that succeeded: (*p* ⨾ *ι*₁) ⊳ (*q* ⨾ *ι*₂). */
  def or[A, B, C](p: P[A, B], q: P[A, C]): P[A, Either[B, C]] = {
    orElse(map(p, coproducts.inl[B, C]), map(q, coproducts.inr[B, C]))
  }

  // ==== Iteration and recursion ====

  /** Runs *p* repeatedly, feeding each right result back as the next semantic input, until it yields a left result:
    * *p*†. A step that yields a right result without consuming input fails the whole loop.
    */
  final def iterate[A, B](p: P[A, Either[B, A]]): P[A, B] = {
    loops.iterate[B, A](p)
  }

  /** The parser *fix*(*f*) defined recursively by *f*, which receives the parser being defined. A recursive call that
    * is not preceded by consumed input fails.
    */
  final def recursive[A, B](f: P[A, B] -> P[A, B]): P[A, B] = {
    knots.fix(f)
  }

  /** A tuple of mutually recursive parsers: *f* receives the tuple being defined and returns its definition. Each
    * component is a knot of [[knots]]' family fixed point, so a call that is not preceded by consumed input fails, and
    * *f* is applied once per application of the family. The tuple may contain only parsers.
    */
  inline def recursive[T <: Tuple](f: T -> T)(using Parsers[T]): T = {
    val n      = compiletime.constValue[Tuple.Size[T]]
    val family = knots.fixFamily[Any, Any](n) { knots =>
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
    mapInput(zip(p, q), products.diagonal[A])
  }

  /** Runs *p*, then *q*, keeping only the result of *q*: ⟨*p*,*q*⟩ ⨾ *π*₂. */
  def skipThen[A, B, C](p: P[A, B], q: P[A, C]): P[A, C] = {
    map(pair(p, q), products.snd[B, C])
  }

  /** Runs *p*, then *q*, keeping only the result of *p*: ⟨*p*,*q*⟩ ⨾ *π*₁. */
  def thenSkip[A, B, C](p: P[A, B], q: P[A, C]): P[A, B] = {
    map(pair(p, q), products.fst[B, C])
  }

  /** Runs *open*, *p*, then *close*, keeping the result of *p*. */
  def between[A, B, C, D](p: P[A, B], open: P[A, C], close: P[A, D]): P[A, B] = {
    thenSkip(skipThen(open, p), close)
  }

  // ==== Repetition: derived from iteration ====

  /** Pairs the semantic input with the empty collection. */
  private def start[A, B]: P[A, (A, Vector[B])] = {
    pure(products.pair(sequencing.category.identity[A], lift[A, Vector[B]](_ => Vector.empty)))
  }

  /** Runs *item* once on the semantic input, appending its result to the collection. */
  private def step[A, B](item: P[A, B]): P[(A, Vector[B]), (A, Vector[B])] = {
    val reshape =
      products.pair(products.fst[A, Vector[B]], products.pair(products.snd[A, Vector[B]], products.fst[A, Vector[B]]))
    val finish = products.parallel(sequencing.category.identity[A], lift[(Vector[B], B), Vector[B]]((bs, b) => bs :+ b))
    map(mapInput(zip(success[A], zip(success[Vector[B]], item)), reshape), finish)
  }

  /** Runs *seed*, then *item* until it fails, collecting the results. */
  private def repeat[A, B](seed: P[A, (A, Vector[B])], item: P[A, B]): P[A, Vector[B]] = {
    val next = map(step(item), coproducts.inr[Vector[B], (A, Vector[B])])
    val done = pure(products.snd[A, Vector[B]] >>> coproducts.inl[Vector[B], (A, Vector[B])])
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
    map(unrolled(p, n), products.snd[A, Vector[B]])
  }

  /** Runs *p* at least *n* times, until it fails, collecting the results. */
  def atLeast[A, B](p: P[A, B], n: Int): P[A, Vector[B]] = {
    repeat(unrolled(p, n), p)
  }

  /** Runs *p* at least once, until it fails, collecting the results: *p*⁺ = *atLeast*(*p*,1). */
  def atLeastOnce[A, B](p: P[A, B]): P[A, Vector[B]] = {
    atLeast(p, 1)
  }

  /** Runs *p* one or more times, separated by *separator*, collecting the results. */
  def separatedBy[A, B, C](p: P[A, B], separator: P[A, C]): P[A, Vector[B]] = {
    repeat(unrolled(p, 1), skipThen(separator, p))
  }

  // ==== Syntax ====

  extension [A, B](p: P[A, B])
    /** Infix extension for [[rule]]. */
    @targetName("ruleExt")
    final def rule(label: String): P[A, B] = ParserAlgebra.this.rule(p, label)

  extension [A, B](p: P[A, B])
    /** Infix extension for [[map]]. */
    @targetName("mapExt")
    final def map[C](g: B --> C): P[A, C] = ParserAlgebra.this.map(p, g)

  extension [A, B](p: P[A, B])
    /** Infix extension for [[mapInput]]. */
    @targetName("mapInputExt")
    final def mapInput[C](f: C --> A): P[C, B] = ParserAlgebra.this.mapInput(p, f)

  extension [A, B](p: P[A, B])
    /** Infix extension for [[andThen]]. */
    final def >>[C](q: P[B, C]): P[A, C] = ParserAlgebra.this.andThen(p, q)

  extension [A, B](p: P[A, B])
    /** Infix extension for [[zip]]. */
    final def **[C, D](q: P[C, D]): P[(A, C), (B, D)] = ParserAlgebra.this.zip(p, q)

  extension [A, B](p: P[A, B])
    /** Infix extension for [[pair]]. */
    final def &&[C](q: P[A, C]): P[A, (B, C)] = ParserAlgebra.this.pair(p, q)

  extension [A, B](p: P[A, B])
    /** Infix extension for [[skipThen]]. */
    final def *>[C](q: P[A, C]): P[A, C] = ParserAlgebra.this.skipThen(p, q)

  extension [A, B](p: P[A, B])
    /** Infix extension for [[thenSkip]]. */
    final def <*[C](q: P[A, C]): P[A, B] = ParserAlgebra.this.thenSkip(p, q)

  extension [A, B](p: P[A, B])
    /** Infix extension for [[between]]. */
    @targetName("betweenExt")
    final def between[C, D](open: P[A, C], close: P[A, D]): P[A, B] = ParserAlgebra.this.between(p, open, close)

  extension [A, B](p: P[A, B])
    /** Infix extension for [[branch]]. */
    final def ++[C, D](q: P[C, D]): P[Either[A, C], Either[B, D]] = ParserAlgebra.this.branch(p, q)

  extension [A, C](p: P[A, C])
    /** Infix extension for [[merge]]. */
    final def ||[B](q: P[B, C]): P[Either[A, B], C] = ParserAlgebra.this.merge(p, q)

  extension [A, B](p: P[A, B])
    /** Infix extension for [[orElse]]. */
    final def |>(q: P[A, B]): P[A, B] = ParserAlgebra.this.orElse(p, q)

  extension [A, B](p: P[A, B])
    /** Infix extension for [[or]]. */
    final def +>[C](q: P[A, C]): P[A, Either[B, C]] = ParserAlgebra.this.or(p, q)

  extension [A, B](p: P[A, B])
    /** Prefix form of [[lookahead]]. */
    final def unary_~ : P[A, A] = ParserAlgebra.this.lookahead(p)

  extension [A, B](p: P[A, B])
    /** Prefix form of [[not]]. */
    final def unary_! : P[A, A] = ParserAlgebra.this.not(p)

  extension [A, B](p: P[A, B])
    /** Postfix form of [[attempt]]. */
    @targetName("attemptExt")
    final def attempt(using DummyImplicit): P[A, Either[B, A]] = ParserAlgebra.this.attempt(p)

  extension [A, B](p: P[A, B])
    /** Postfix form of [[optional]]. */
    @targetName("optionalExt")
    final def optional(using DummyImplicit): P[A, Either[B, A]] = ParserAlgebra.this.optional(p)

  extension [A, B](p: P[A, B])
    /** Postfix form of [[optional]]. */
    final def ? : P[A, Either[B, A]] = ParserAlgebra.this.optional(p)

  extension [A, B](p: P[A, B])
    /** Postfix form of [[repeated]]. */
    @targetName("repeatedExt")
    final def repeated(using DummyImplicit): P[A, Vector[B]] = ParserAlgebra.this.repeated(p)

  extension [A, B](p: P[A, B])
    /** Postfix form of [[repeated]]. */
    final def * : P[A, Vector[B]] = ParserAlgebra.this.repeated(p)

  extension [A, B](p: P[A, B])
    /** Postfix form of [[atLeastOnce]]. */
    @targetName("atLeastOnceExt")
    final def atLeastOnce(using DummyImplicit): P[A, Vector[B]] = ParserAlgebra.this.atLeastOnce(p)

  extension [A, B](p: P[A, B])
    /** Postfix form of [[atLeastOnce]]. */
    final def + : P[A, Vector[B]] = ParserAlgebra.this.atLeastOnce(p)

  extension [A, B](p: P[A, B])
    /** Infix extension for [[times]]. */
    @targetName("timesExt")
    final def times(n: Int): P[A, Vector[B]] = ParserAlgebra.this.times(p, n)

  extension [A, B](p: P[A, B])
    /** Infix extension for [[atLeast]]. */
    @targetName("atLeastExt")
    final def atLeast(n: Int): P[A, Vector[B]] = ParserAlgebra.this.atLeast(p, n)

  extension [A, B](p: P[A, B])
    /** Infix extension for [[separatedBy]]. */
    @targetName("separatedByExt")
    final def separatedBy[C](separator: P[A, C]): P[A, Vector[B]] = ParserAlgebra.this.separatedBy(p, separator)

  extension [A, B](p: P[A, Either[B, A]])
    /** Postfix form of [[iterate]]. */
    @targetName("iterateExt")
    final def iterate(using DummyImplicit): P[A, B] = ParserAlgebra.this.iterate(p)

  /** The equations of parsing expression grammars, in the vocabulary of parsers. Most are laws of the structures the
    * algebra is built from. Checking the laws on the combinators also checks the overrides of interpreters.
    *
    * The laws come in two tiers. Equations hold for results, offsets and diagnostics, observed with an [[Observable]].
    * Inequations *p* ⊑ *q* say that *p* and *q* have the same results and offsets and that *q* reports at least what
    * *p* reports, observed with a [[Preorder]]. These are equations that only hold up to diagnostics, because a silent
    * lookahead or a failure forgets what the parser before it expected. Every combinator preserves ⊑, so parsers are
    * enriched over preorders.
    */
  object ParserLaws {

    /** *id* ⨾ *p* = *p*
      */
    def leftIdentity[A, B](p: P[A, B])(using P[A, B] is Observable): Boolean = {
      (success[A] >> p) =?= p
    }

    /** *p* ⨾ *id* = *p*
      */
    def rightIdentity[A, B](p: P[A, B])(using P[A, B] is Observable): Boolean = {
      (p >> success[B]) =?= p
    }

    /** (*p* ⨾ *q*) ⨾ *r* = *p* ⨾ (*q* ⨾ *r*) */
    def associativity[A, B, C, D](p: P[A, B], q: P[B, C], r: P[C, D])(using P[A, D] is Observable): Boolean = {
      ((p >> q) >> r) =?= (p >> (q >> r))
    }

    /** *id* ⋉ *id* = *id*
      */
    def zipIdentity[A, C](using P[(A, C), (A, C)] is Observable): Boolean = {
      (success[A] ** success[C]) =?= success[(A, C)]
    }

    /** *zip*(*p*,*q*) = *p* ⋉ *q* in [[zipped]]
      */
    def zipDefinition[A, B, C, D](p: P[A, B], q: P[C, D])(using P[(A, C), (B, D)] is Observable): Boolean = {
      (p ** q) =?= zipped.leftToRight(p, q)
    }

    /** *branch*(*p*,*q*) = *p* + *q* in [[branched]]
      */
    def branchDefinition[A, B, C, D](p: P[A, B], q: P[C, D])(
      using P[Either[A, C], Either[B, D]] is Observable
    ): Boolean = {
      (p ++ q) =?= branched.leftToRight(p, q)
    }

    /** *map*(*p*,*g*) = *p* ⨾ *unit*(*g*)
      */
    def mapDefinition[A, B, C](p: P[A, B], g: B --> C)(using P[A, C] is Observable): Boolean = {
      map(p, g) =?= andThen(p, pure(g))
    }

    /** *mapInput*(*p*,*f*) = *unit*(*f*) ⨾ *p*
      */
    def mapInputDefinition[A, B, C](p: P[A, B], f: C --> A)(using P[C, B] is Observable): Boolean = {
      mapInput(p, f) =?= andThen(pure(f), p)
    }

    /** [*p*,*q*] = (*p* + *q*) ⨾ *unit*(∇)
      */
    def mergeDefinition[A, B, C](p: P[A, C], q: P[B, C])(using P[Either[A, B], C] is Observable): Boolean = {
      merge(p, q) =?= map(branch(p, q), coproducts.codiagonal[C])
    }

    /** *or*(*p*,*q*) = (*p* ⨾ *ι*₁) ⊳ (*q* ⨾ *ι*₂)
      */
    def orDefinition[A, B, C](p: P[A, B], q: P[A, C])(using P[A, Either[B, C]] is Observable): Boolean = {
      or(p, q) =?= orElse(map(p, coproducts.inl[B, C]), map(q, coproducts.inr[B, C]))
    }

    /** ⟨*p*,*q*⟩ = *unit*(Δ) ⨾ (*p* ⋉ *q*)
      */
    def pairDefinition[A, B, C](p: P[A, B], q: P[A, C])(using P[A, (B, C)] is Observable): Boolean = {
      pair(p, q) =?= mapInput(zip(p, q), products.diagonal[A])
    }

    /** *skipThen*(*p*,*q*) = ⟨*p*,*q*⟩ ⨾ *unit*(*π*₂)
      */
    def skipThenDefinition[A, B, C](p: P[A, B], q: P[A, C])(using P[A, C] is Observable): Boolean = {
      skipThen(p, q) =?= map(pair(p, q), products.snd[B, C])
    }

    /** *thenSkip*(*p*,*q*) = ⟨*p*,*q*⟩ ⨾ *unit*(*π*₁)
      */
    def thenSkipDefinition[A, B, C](p: P[A, B], q: P[A, C])(using P[A, B] is Observable): Boolean = {
      thenSkip(p, q) =?= map(pair(p, q), products.fst[B, C])
    }

    /** *between*(*p*,*open*,*close*) = *thenSkip*(*skipThen*(*open*,*p*),*close*)
      */
    def betweenDefinition[A, B, C, D](p: P[A, B], open: P[A, C], close: P[A, D])(
      using P[A, B] is Observable
    ): Boolean = {
      between(p, open, close) =?= thenSkip(skipThen(open, p), close)
    }

    /** 0 ⨾ *p* = 0: nothing runs after a failure. */
    def leftZero[A, B, C](p: P[B, C])(using P[A, C] is Observable): Boolean = {
      (failure[A, B] >> p) =?= failure[A, C]
    }

    /** 0 ⊑ *p* ⨾ 0: a failure at the end fails the whole sequence, which still reports what *p* expected.
      */
    def rightZero[A, B, C](p: P[A, B])(using P[A, C] is Preorder): Boolean = {
      failure[A, C] ?< (p >> failure[B, C])
    }

    /** 0 ⊳ *p* = *p* = *p* ⊳ 0 */
    def choiceIdentity[A, B](p: P[A, B])(using P[A, B] is Observable): Boolean = {
      ((failure[A, B] |> p) =?= p) && ((p |> failure[A, B]) =?= p)
    }

    /** (*p* ⊳ *q*) ⊳ *r* = *p* ⊳ (*q* ⊳ *r*) */
    def choiceAssociativity[A, B](p: P[A, B], q: P[A, B], r: P[A, B])(using P[A, B] is Observable): Boolean = {
      ((p |> q) |> r) =?= (p |> (q |> r))
    }

    /** *h* ⨾ (*p* ⊳ *q*) = (*h* ⨾ *p*) ⊳ (*h* ⨾ *q*): choice distributes over what comes before it.
      */
    def choicePrecomposition[A, B, C](h: P[A, B], p: P[B, C], q: P[B, C])(using P[A, C] is Observable): Boolean = {
      (h >> (p |> q)) =?= ((h >> p) |> (h >> q))
    }

    /** *attempt*(*p*) = (*p* ⨾ *ι*₁) ⊳ *ι*₂
      */
    def attemptDefinition[A, B](p: P[A, B])(using P[A, Either[B, A]] is Observable): Boolean = {
      attempt(p) =?= (map(p, coproducts.inl[B, A]) |> pure(coproducts.inr[B, A]))
    }

    /** *p* ⊳ *q* = *attempt*(*p*) ⨾ [*id*,*q*]: ordered choice is an attempt followed by a merge.
      */
    def choiceByAttempt[A, B](p: P[A, B], q: P[A, B])(using P[A, B] is Observable): Boolean = {
      (p |> q) =?= (attempt(p) >> (success[B] || q))
    }

    /** *p̄* ⨾ *p* ⊑ *p* (**R1**, up to diagnostics): where *p* fails, the silent lookahead reports nothing.
      */
    def lookaheadIdentity[A, B](p: P[A, B])(using P[A, B] is Preorder): Boolean = {
      (~p >> p) ?< p
    }

    /** *p̄* ⨾ *q̄* = *q̄* ⨾ *p̄* (**R2**)
      */
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
      (~(p >> q) >> p) ?< (p >> ~q)
    }

    /** (*p̄*ᶜ)ᶜ = *p̄* */
    def doubleNegation[A, B](p: P[A, B])(using P[A, A] is Observable): Boolean = {
      !(!p) =?= ~p
    }

    /** *p̄* ⨾ *p̄*ᶜ = 0: a parser cannot both succeed and fail.
      */
    def negationExclusion[A, B](p: P[A, B])(using P[A, A] is Observable): Boolean = {
      (~p >> !p) =?= failure[A, A]
    }

    /** *p̄* ⊳ *p̄*ᶜ = *id*: a parser either succeeds or fails.
      */
    def negationCover[A, B](p: P[A, B])(using P[A, A] is Observable): Boolean = {
      (~p |> !p) =?= success[A]
    }

    /** *p*† = *p* ⨾ [*id*,*p*†]
      *
      * @note Holds for a guarded *p*, whose steps consume input whenever they continue. The premise is not checked.
      */
    def loopUnfolding[A, B](p: P[A, Either[B, A]])(using P[A, B] is Observable): Boolean = {
      p.iterate =?= (p >> (success[B] || p.iterate))
    }

    /** *fix*(*f*) = *f*(*fix*(*f*))
      *
      * @note Holds for a guarded *f*, which calls its argument only after consuming input. The premise is not
      *   checked.
      */
    def recursionUnfolding[A, B](f: P[A, B] -> P[A, B])(using P[A, B] is Observable): Boolean = {
      recursive(f) =?= f(recursive(f))
    }

    /** *rule*(*p*,*l*) = *p*: rules change diagnostics only.
      *
      * @note Holds for results and offsets: the observation must not include diagnostics.
      */
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
      (p >> q) ?< (p2 >> q2)
    }

    /** If *p* ⊑ *p*′ and *q* ⊑ *q*′, then *p* ⊳ *q* ⊑ *p*′ ⊳ *q*′.
      *
      * @note The premise is not checked: *p*′ and *q*′ must be built to report more than *p* and *q*.
      */
    def orElseMonotone[A, B](p: P[A, B], p2: P[A, B], q: P[A, B], q2: P[A, B])(using P[A, B] is Preorder): Boolean = {
      (p |> q) ?< (p2 |> q2)
    }

    /** If *p* ⊑ *p*′ and *q* ⊑ *q*′, then *p* ⋉ *q* ⊑ *p*′ ⋉ *q*′.
      *
      * @note The premise is not checked: *p*′ and *q*′ must be built to report more than *p* and *q*.
      */
    def zipMonotone[A, B, C, D](p: P[A, B], p2: P[A, B], q: P[C, D], q2: P[C, D])(
      using P[(A, C), (B, D)] is Preorder
    ): Boolean = {
      (p ** q) ?< (p2 ** q2)
    }

    /** If *p* ⊑ *p*′ and *q* ⊑ *q*′, then *p* + *q* ⊑ *p*′ + *q*′.
      *
      * @note The premise is not checked: *p*′ and *q*′ must be built to report more than *p* and *q*.
      */
    def branchMonotone[A, B, C, D](p: P[A, B], p2: P[A, B], q: P[C, D], q2: P[C, D])(
      using P[Either[A, C], Either[B, D]] is Preorder
    ): Boolean = {
      (p ++ q) ?< (p2 ++ q2)
    }

    /** If *p* ⊑ *p*′, then *p*† ⊑ *p*′†.
      *
      * @note The premise is not checked: *p*′ must be built to report more than *p*.
      */
    def iterateMonotone[A, B](p: P[A, Either[B, A]], p2: P[A, Either[B, A]])(using P[A, B] is Preorder): Boolean = {
      p.iterate ?< p2.iterate
    }

    /** If *p* ⊑ *p*′, then *attempt*(*p*) ⊑ *attempt*(*p*′).
      *
      * @note The premise is not checked: *p*′ must be built to report more than *p*.
      */
    def attemptMonotone[A, B](p: P[A, B], p2: P[A, B])(using P[A, Either[B, A]] is Preorder): Boolean = {
      p.attempt ?< p2.attempt
    }

    /** If *p* ⊑ *p*′, then *p̄* ⊑ *p*′‾: both are silent, and they succeed on the same inputs.
      *
      * @note The premise is not checked: *p*′ must be built to report more than *p*.
      */
    def lookaheadMonotone[A, B](p: P[A, B], p2: P[A, B])(using P[A, A] is Preorder): Boolean = {
      ~p ?< ~p2
    }

    /** If *p* ⊑ *p*′, then *p̄*ᶜ ⊑ *p*′‾ᶜ: both are silent, and they succeed on the same inputs.
      *
      * @note The premise is not checked: *p*′ must be built to report more than *p*.
      */
    def notMonotone[A, B](p: P[A, B], p2: P[A, B])(using P[A, A] is Preorder): Boolean = {
      !p ?< !p2
    }

    /** If *p* ⊑ *p*′, then *rule*(*p*,*l*) ⊑ *rule*(*p*′,*l*).
      *
      * @note The premise is not checked: *p*′ must be built to report more than *p*.
      */
    def ruleMonotone[A, B](p: P[A, B], p2: P[A, B], label: String)(using P[A, B] is Preorder): Boolean = {
      p.rule(label) ?< p2.rule(label)
    }

    /** *p*\* = (⟨*p*,*p*\*⟩ ⨾ *unit*(*cons*)) ⊳ *unit*(*empty*), where *cons* prepends a result to the collection and
      * *empty* is the empty collection.
      *
      * @note Holds for a *p* that consumes input whenever it succeeds. The premise is not checked.
      */
    def repeatedUnfolding[A, B](p: P[A, B])(using P[A, Vector[B]] is Observable): Boolean = {
      val cons  = lift[(B, Vector[B]), Vector[B]]((b, bs) => b +: bs)
      val empty = lift[A, Vector[B]](_ => Vector.empty)
      p.repeated =?= ((p && p.repeated).map(cons) |> pure(empty))
    }

    /** *p*⁺ = *atLeast*(*p*,1) */
    def atLeastOnceDefinition[A, B](p: P[A, B])(using P[A, Vector[B]] is Observable): Boolean = {
      atLeastOnce(p) =?= atLeast(p, 1)
    }

    /** *p*\* = the loop that runs *p* until it fails, from the empty collection
      *
      * The loop is the iteration of (*step*(*p*) ⨾ *ι*₂) ⊳ (*π*₂ ⨾ *ι*₁), where *step*(*p*) runs *p* on the semantic
      * input and appends its result to the collection.
      */
    def repeatedDefinition[A, B](p: P[A, B])(using P[A, Vector[B]] is Observable): Boolean = {
      repeated(p) =?= repeat(start[A, B], p)
    }

    /** *times*(*p*,*n*) = *step*(*p*)ⁿ ⨾ *unit*(*π*₂), from the empty collection
      */
    def timesDefinition[A, B](p: P[A, B], n: Int)(using P[A, Vector[B]] is Observable): Boolean = {
      times(p, n) =?= map(unrolled(p, n), products.snd[A, Vector[B]])
    }

    /** *atLeast*(*p*,*n*) = the loop that runs *p* until it fails, from *step*(*p*)ⁿ
      */
    def atLeastDefinition[A, B](p: P[A, B], n: Int)(using P[A, Vector[B]] is Observable): Boolean = {
      atLeast(p, n) =?= repeat(unrolled(p, n), p)
    }

    /** *separatedBy*(*p*,*s*) = the loop that runs *skipThen*(*s*,*p*) until it fails, from *step*(*p*)
      */
    def separatedByDefinition[A, B, C](p: P[A, B], separator: P[A, C])(using P[A, Vector[B]] is Observable): Boolean = {
      separatedBy(p, separator) =?= repeat(unrolled(p, 1), skipThen(separator, p))
    }
  }
}
