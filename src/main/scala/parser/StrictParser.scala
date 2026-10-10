package parrot
package parser

import parrot.category.{Elgot, Enriched, Fixed, Monoid, Promonad, Restriction, Strong, Cocartesian}

import java.util.regex.{Matcher, Pattern as JPattern}
import scala.util.matching.Regex

/** A specialized interpreter of [[ParserAlgebra]] that normalizes parsers at construction time and runs them without
  * allocating intermediate structure.
  *
  * Parsers are reified terms ([[Node]]) over reified pure functions ([[Fn]]). Instead of the structural mixins, every
  * primitive is implemented directly as a smart constructor that rewrites its arguments towards a normal form, so the
  * *derived* mixins collapse into specialized nodes. For example
  *   - `p.pair(q)` = `p.zip(q).mapInput(Δ)` becomes `Pair(p, q)`: the input is never duplicated into a tuple
  *   - `p.skipThen(q)` = `Pair(p, q).map(π₂)` becomes `SkipThen(p, q)`: no result tuple is built
  *   - `p.branch(q).map([f, g])` becomes `Merge(p.map(f), q.map(g))`: no intermediate `Either` is built
  *   - `(p orElse q).map(f)` becomes `p.map(f) orElse q.map(f)`, which holds because `f` is pure and total, so that
  *     `(p or q).map([f, g])` becomes `p.map(f) orElse q.map(g)`: again no intermediate `Either` is built
  *   - `p.zip(success)` becomes `First(p)`
  *
  * Combinators whose derivation cannot be fused this way (`not`, repetition) are implemented with dedicated nodes. At
  * run time, a single mutable [[State]] carries the position, and failure is signalled by an unboxed [[Out]] instead
  * of a result wrapper.
  *
  * ==Lexical and choice optimizations==
  *
  *   - Regular expressions that are concatenations of (quantified) character classes, such as `[0-9]+` or
  *     `[1-9][0-9]*`, are compiled to a [[Scanner]] that runs without `java.util.regex`; other expressions reuse one
  *     `Matcher` per pattern and run.
  *   - Nested ordered choices are flattened into one [[Node.Choice]], which dispatches on the next character: a static
  *     analysis ([[Info]]) computes for each alternative the characters it can start with, and alternatives that cannot
  *     succeed on the next character are skipped without being run.
  *   - Failure messages are computed once, at construction time.
  *
  * ==Recursion==
  *
  * `recursive` ties a knot ([[Node.Rec]]) and supports left recursion by '''seed growing''' (Warth et al., "Packrat
  * Parsers Can Support Left Recursion"), ported from the legacy interpreter: when a recursive parser re-enters itself
  * at the same position with the same semantic input, the inner call returns the current *seed* (initially a failure),
  * and the outer call re-runs its body as long as the result consumes strictly more input. Without left recursion this
  * computes the same (least) fixed point as [[ReferenceParser]], but costs no memo table: only the active recursive
  * calls are tracked. With left recursion the result is a different fixed point, which breaks the Conway laws of the
  * [[ParserAlgebra.Recursion]] mixin whenever ordered choice or negation make the definition non-monotone.
  *
  * Unlike the legacy interpreter, `rule` does not memoize: there is no packrat cache, so backtracking may re-run
  * parsers, just as in [[ReferenceParser]].
  *
  * ==Strictness of the unit==
  *
  * The unit is strict *on terms*, not *on types*: `Pair` stays `Tuple2` and `Empty` stays `Unit`, while the unitors and
  * projections that witness *I* ⊗ *A* ≅ *A* are eliminated by normalization before any tuple is built. Making it strict
  * on types with a match type (`Pair[Unit, B] = B`, `Pair[A, Unit] = A`, otherwise `(A, B)`) is unsound for the generic
  * mixins: the projection *π*₂: *A* ⊗ *B* ==> *B* is not determined by its (reduced) type. Its runtime value must be
  * `identity` at `Pair[Unit, (X, Y)]` but `_._2` at `Pair[X, Y]`, which both reduce to `(X, Y)` and share a
  * representation. Parametric code such as `Pairing` constructs *π*₂ with *A* and *B* abstract (where the match type is
  * stuck), so it cannot choose. A type-strict variant would need shape-indexed morphisms (`Shape[A]` evidence on every
  * projection and on [[zip]]), which the assumption-free root signatures deliberately do not carry. By Mac Lane's
  * coherence theorem, normalizing the structural morphisms is equivalent and stays parametric.
  *
  * ==Deviations from the reference==
  *
  *   - Repetitions stop after an iteration that consumes no input, where the reference diverges.
  *   - Left recursion succeeds by seed growing, where the reference diverges.
  *   - When several failures happen at the same furthest position, the reported expectation may differ.
  */
object StrictParser extends ParserAlgebra, ParserAlgebra.Pairing {

  type Self[A, B]        = Node[A, B]
  type On[A, B]          = Fn[A, B]
  type Empty             = Unit
  type Pair[A, B]        = (A, B)
  type None              = Nothing
  type Alternative[A, B] = Either[A, B]
  type Many[B]           = Vector[B]

  override val OnIsCartesian: Fn.FnIsCartesian.type = Fn.FnIsCartesian

  // ===========================================================================
  // Runtime
  // ===========================================================================

  /** The result of running a node: a value of `B`, or a failure. */
  type Out[+B] = Out.Out[B]

  object Out {

    /** Unboxed: either a value of `B` itself, or the failure sentinel. */
    opaque type Out[+B] = Any

    private object Failed

    val failed: Out[Nothing] = Failed

    inline def apply[B](value: B): Out[B] = value

    extension [B](out: Out[B])
      inline def isFailed: Boolean = out.isInstanceOf[Failed.type]

      /** The value of a successful `out`. */
      inline def get: B = out.asInstanceOf[B]
  }

  /** An active call of the recursive parser `rec` on `arg` at `start`, with the seed it grows if it turns out to be
    * left-recursive.
    */
  final private class Head[A, B](val rec: Node.Rec[A, B], val arg: A, val start: Int) {
    var seed: Out[B]           = Out.failed
    var seedEnd: Int           = start
    var leftRecursive: Boolean = false
  }

  /** The mutable state of a single run: the current position, the furthest failure, the regex matchers and the stack of
    * active recursive calls.
    */
  final class State(val source: String) {
    var offset: Int      = 0
    var failedAt: Int    = -1
    var expected: String = ""

    def fail(label: String): Out[Nothing] = {
      if offset > failedAt then {
        failedAt = offset
        expected = label
      }
      Out.failed
    }

    private val matchers = java.util.IdentityHashMap[JPattern, Matcher]()

    /** The matcher of `pattern` on the source, created once per run. */
    def matcher(pattern: JPattern): Matcher = {
      val cached = matchers.get(pattern)
      if cached != null then cached
      else {
        val created = pattern.matcher(source).nn
        val _       = matchers.put(pattern, created)
        created
      }
    }

    /** The active recursive calls, whose positions are non-decreasing because nested calls never start before their
      * callers.
      */
    private var heads: Array[Head[?, ?] | Null] = new Array(16)
    private var depth: Int                      = 0

    /** The active call of `rec` on `arg` at position `at`. */
    private[StrictParser] def findHead[A, B](rec: Node.Rec[A, B], arg: A, at: Int): Head[A, B] | Null = {
      var i = depth - 1
      while i >= 0 && heads(i).nn.start == at do {
        val head = heads(i).nn
        // a head of the same knot has the same types
        if (head.rec eq rec) && java.util.Objects.equals(head.arg, arg) then return head.asInstanceOf[Head[A, B]]
        i -= 1
      }
      null
    }

    private[StrictParser] def pushHead[A, B](rec: Node.Rec[A, B], arg: A, at: Int): Head[A, B] = {
      if depth == heads.length then heads = java.util.Arrays.copyOf(heads, depth * 2).nn
      val head = Head(rec, arg, at)
      heads(depth) = head
      depth += 1
      head
    }

    private[StrictParser] def popHead(): Unit = {
      depth -= 1
      heads(depth) = null
    }
  }

  extension [B](self: P[Unit, B])
    /** Runs `self` on a prefix of `source`. */
    def parse(source: String): Either[(offset: Int, expected: String), (value: B, offset: Int)] = {
      val state = State(source)
      val out   = self.run((), state)
      if out.isFailed then Left((offset = state.failedAt, expected = state.expected))
      else Right((value = out.get, offset = state.offset))
    }

    /** Runs `self` on the whole of `source`. */
    def parseAll(source: String): Either[(offset: Int, expected: String), (value: B, offset: Int)] = {
      self.thenSkip(endOfInput).parse(source)
    }

  private lazy val endOfInput: P[Unit, Unit] = regex("(?s).".r).not

  // ===========================================================================
  // Static analysis
  // ===========================================================================

  /** What a parser can start with: if it succeeds where the next character is `c` (or at the end of the input), then it
    * is `nullable` or `c` is in `first`.
    *
    * `nullable` parsers may succeed without consuming anything, whatever comes next.
    */
  final case class Info(first: CharSet, nullable: Boolean) {
    def orElse(that: Info): Info = Info(first.union(that.first), nullable || that.nullable)

    def andThen(that: => Info): Info = if nullable then Info(first.union(that.first), that.nullable) else this
  }

  object Info {
    given CanEqual[Info, Info] = CanEqual.derived

    /** Never succeeds. */
    val never: Info = Info(CharSet.empty, false)

    /** May succeed anywhere. */
    val unknown: Info = Info(CharSet.empty, true)

    /** The analysis of `node`, with recursive knots solved by Kleene iteration from [[never]]. */
    def of[A, B](node: Node[A, B]): Info = analyze(node, java.util.IdentityHashMap())

    /** `env` holds the current approximations of the knots being solved, of any types. */
    private def analyze[A, B](node: Node[A, B], env: java.util.IdentityHashMap[Node.Rec[?, ?], Info]): Info = {
      import Node.*
      node match {
        case Rule(_, p)        => analyze(p, env)
        case Literal(expected) =>
          if expected.isEmpty then unknown else Info(CharSet.of(expected.charAt(0)), false)
        case Scan(_, scanner)                          => Info(scanner.first.set, scanner.first.nullable)
        case Pattern(_) | Pure(_) | Success() | Not(_) => unknown
        case Failure()                                 => never
        case Seq(p, q)                                 => analyze(p, env).andThen(analyze(q, env))
        case Zip(p, q)                                 => analyze(p, env).andThen(analyze(q, env))
        case Pair(p, q)                                => analyze(p, env).andThen(analyze(q, env))
        case SkipThen(p, q)                            => analyze(p, env).andThen(analyze(q, env))
        case ThenSkip(p, q)                            => analyze(p, env).andThen(analyze(q, env))
        case First(p)                                  => analyze(p, env)
        case Lookahead(p)                              => analyze(p, env)
        case Loop(p)                                   => analyze(p, env)
        case Branch(p, q)                              => analyze(p, env).orElse(analyze(q, env))
        case Merge(p, q)                               => analyze(p, env).orElse(analyze(q, env))
        case Choice(alternatives)                      => alternatives.map(analyze(_, env)).reduce(_.orElse(_))
        case Repeat(p, min, _, _)                      =>
          val item = analyze(p, env)
          if min == 0 || item.nullable then unknown else item
        case rec: Rec[A, B] =>
          val assumed = env.get(rec)
          if assumed != null then assumed
          else if rec.info ne null then rec.info.nn
          else {
            var current = never
            var stable  = false
            while !stable do {
              val _    = env.put(rec, current)
              val next = analyze(rec.body.nn, env)
              stable = next == current
              current = next
            }
            val _ = env.remove(rec)
            if env.isEmpty then rec.info = current
            current
          }
      }
    }

    /** The message of the first failure that `node` would report when it fails without consuming anything. `visited`
      * holds the knots already unfolded, of any types.
      */
    def label[A, B](node: Node[A, B], visited: Set[Node.Rec[?, ?]] = Set.empty): Option[String] = {
      import Node.*
      node match {
        case Rule(label, _)       => Some(label)
        case l: Literal           => Option.when(l.expected.nonEmpty)(l.label)
        case s: Scan              => Some(s.label)
        case p: Pattern           => Some(p.label)
        case Failure()            => Some("failure")
        case Not(p)               => label(p, visited).orElse(Some("not"))
        case Seq(p, q)            => label(p, visited).orElse(label(q, visited))
        case Pair(p, q)           => label(p, visited).orElse(label(q, visited))
        case SkipThen(p, q)       => label(p, visited).orElse(label(q, visited))
        case ThenSkip(p, q)       => label(p, visited).orElse(label(q, visited))
        case Zip(p, q)            => label(p, visited).orElse(label(q, visited))
        case First(p)             => label(p, visited)
        case Lookahead(p)         => label(p, visited)
        case Loop(p)              => label(p, visited)
        case Repeat(p, _, _, _)   => label(p, visited)
        case Choice(alternatives) => alternatives.iterator.map(label(_, visited)).collectFirst { case Some(l) => l }
        case rec: Rec[A, B] if !visited.contains(rec) => label(rec.body.nn, visited + rec)
        case _                                        => scala.None
      }
    }
  }

  // ===========================================================================
  // Reified parsers
  // ===========================================================================

  /** A reified parser. */
  sealed trait Node[A, B] {
    def run(a: A, s: State): Out[B]
  }

  object Node {
    final case class Rule[A, B](label: String, p: Node[A, B]) extends Node[A, B] {
      def run(a: A, s: State): Out[B] = {
        val start = s.offset
        val out   = p.run(a, s)
        if out.isFailed && s.failedAt == start then s.expected = label
        out
      }
    }

    final case class Literal(expected: String) extends Node[Unit, String] {
      private[StrictParser] val label: String = s"\"$expected\""
      private val length                      = expected.length
      private val head                        = if length > 0 then expected.charAt(0) else '\u0000'

      def run(a: Unit, s: State): Out[String] = {
        val offset = s.offset
        val source = s.source
        if length == 0 then Out(expected)
        else if offset < source.length && source.charAt(offset) == head &&
          (length == 1 || source.startsWith(expected, offset))
        then {
          s.offset = offset + length
          Out(expected)
        } else s.fail(label)
      }
    }

    /** A regular expression compiled to a [[Scanner]]. */
    final case class Scan(expected: Regex, scanner: Scanner) extends Node[Unit, String] {
      private[StrictParser] val label: String = s"/${expected.regex}/"

      def run(a: Unit, s: State): Out[String] = {
        val start = s.offset
        val end   = scanner.scan(s.source, start)
        if end < 0 then s.fail(label)
        else {
          s.offset = end
          Out(s.source.substring(start, end).nn)
        }
      }
    }

    /** A regular expression run by `java.util.regex`. */
    final case class Pattern(expected: Regex) extends Node[Unit, String] {
      private[StrictParser] val label: String = s"/${expected.regex}/"
      private val pattern                     = expected.pattern

      def run(a: Unit, s: State): Out[String] = {
        val start   = s.offset
        val matcher = s.matcher(pattern).region(start, s.source.length).nn
        if matcher.lookingAt() then {
          s.offset = matcher.end()
          Out(s.source.substring(start, s.offset).nn)
        } else s.fail(label)
      }
    }

    final case class Pure[A, B](f: Fn[A, B]) extends Node[A, B] {
      def run(a: A, s: State): Out[B] = Out(f(a))
    }

    final case class Success[A]() extends Node[A, A] {
      def run(a: A, s: State): Out[A] = Out(a)
    }

    final case class Failure[A, B]() extends Node[A, B] {
      def run(a: A, s: State): Out[B] = s.fail("failure")
    }

    final case class Seq[A, B, C](p: Node[A, B], q: Node[B, C]) extends Node[A, C] {
      def run(a: A, s: State): Out[C] = {
        val b = p.run(a, s)
        if b.isFailed then Out.failed else q.run(b.get, s)
      }
    }

    final case class Zip[A, B, C, D](p: Node[A, B], q: Node[C, D]) extends Node[(A, C), (B, D)] {
      def run(ac: (A, C), s: State): Out[(B, D)] = {
        val b = p.run(ac._1, s)
        if b.isFailed then Out.failed
        else {
          val d = q.run(ac._2, s)
          if d.isFailed then Out.failed else Out((b.get, d.get))
        }
      }
    }

    final case class First[A, B, C](p: Node[A, B]) extends Node[(A, C), (B, C)] {
      def run(ac: (A, C), s: State): Out[(B, C)] = {
        val b = p.run(ac._1, s)
        if b.isFailed then Out.failed else Out((b.get, ac._2))
      }
    }

    final case class Pair[A, B, C](p: Node[A, B], q: Node[A, C]) extends Node[A, (B, C)] {
      def run(a: A, s: State): Out[(B, C)] = {
        val b = p.run(a, s)
        if b.isFailed then Out.failed
        else {
          val c = q.run(a, s)
          if c.isFailed then Out.failed else Out((b.get, c.get))
        }
      }
    }

    final case class SkipThen[A, B, C](p: Node[A, B], q: Node[A, C]) extends Node[A, C] {
      def run(a: A, s: State): Out[C] = {
        if p.run(a, s).isFailed then Out.failed else q.run(a, s)
      }
    }

    final case class ThenSkip[A, B, C](p: Node[A, B], q: Node[A, C]) extends Node[A, B] {
      def run(a: A, s: State): Out[B] = {
        val b = p.run(a, s)
        if b.isFailed || q.run(a, s).isFailed then Out.failed else b
      }
    }

    final case class Branch[A, B, C, D](p: Node[A, B], q: Node[C, D]) extends Node[Either[A, C], Either[B, D]] {
      def run(ac: Either[A, C], s: State): Out[Either[B, D]] = ac match {
        case Left(a) =>
          val b = p.run(a, s)
          if b.isFailed then Out.failed else Out(Left(b.get))
        case Right(c) =>
          val d = q.run(c, s)
          if d.isFailed then Out.failed else Out(Right(d.get))
      }
    }

    final case class Merge[A, B, C](p: Node[A, C], q: Node[B, C]) extends Node[Either[A, B], C] {
      def run(ab: Either[A, B], s: State): Out[C] = ab match {
        case Left(a)  => p.run(a, s)
        case Right(b) => q.run(b, s)
      }
    }

    /** The alternatives to try, in order, for one class of next characters. `skipsFirst` is set if the first
      * alternative is not among them, so that its failure is reported as the reference would.
      */
    final private class Candidates[A, B](val nodes: Array[Node[A, B]], val skipsFirst: Boolean)

    /** The candidates for each ASCII character, any other character, and the end of the input. */
    final private class Dispatch[A, B](alternatives: List[Node[A, B]]) {
      private val all   = alternatives.toArray
      private val infos = all.map(Info.of)
      val label: String = Info.label(all(0)).getOrElse("failure")

      private def select(admits: Info => Boolean): Candidates[A, B] = {
        val chosen = all.indices.filter(i => admits(infos(i)))
        Candidates(chosen.map(all).toArray, !chosen.contains(0))
      }

      val ascii: Array[Candidates[A, B]] =
        Array.tabulate(128)(c => select(i => i.nullable || i.first.contains(c.toChar)))
      val other: Candidates[A, B] = select(i => i.nullable || i.first.hasNonAscii)
      val end: Candidates[A, B]   = select(_.nullable)
    }

    /** Ordered choice between two or more alternatives, dispatching on the next character. */
    final case class Choice[A, B](alternatives: List[Node[A, B]]) extends Node[A, B] {
      private lazy val dispatch = Dispatch(alternatives)

      def run(a: A, s: State): Out[B] = {
        val start      = s.offset
        val source     = s.source
        val table      = dispatch
        val candidates =
          if start >= source.length then table.end
          else {
            val c = source.charAt(start)
            if c < 128 then table.ascii(c) else table.other
          }
        if candidates.skipsFirst then {
          val _ = s.fail(table.label)
        }
        val nodes = candidates.nodes
        var i     = 0
        while i < nodes.length do {
          val out = nodes(i).run(a, s)
          if !out.isFailed then return out
          s.offset = start
          i += 1
        }
        Out.failed
      }
    }

    final case class Lookahead[A, B](p: Node[A, B]) extends Node[A, A] {
      def run(a: A, s: State): Out[A] = {
        val start = s.offset
        if p.run(a, s).isFailed then Out.failed
        else {
          s.offset = start
          Out(a)
        }
      }
    }

    final case class Not[A, B](p: Node[A, B]) extends Node[A, A] {
      def run(a: A, s: State): Out[A] = {
        val start = s.offset
        val out   = p.run(a, s)
        s.offset = start
        if out.isFailed then Out(a) else s.fail("not")
      }
    }

    final case class Loop[A, B](p: Node[A, Either[B, A]]) extends Node[A, B] {
      def run(a: A, s: State): Out[B] = {
        var next: A = a
        while true do {
          val out = p.run(next, s)
          if out.isFailed then return Out.failed
          out.get match {
            case Left(b)  => return Out(b)
            case Right(a) => next = a
          }
        }
        Out.failed
      }
    }

    /** Runs `p` between `min` and `max` times, separated by `separator`, whose result is discarded.
      *
      * Stops early when an iteration consumes no input, where the reference interpreter diverges.
      */
    final case class Repeat[A, B](p: Node[A, B], min: Int, max: Int, separator: Option[Node[A, ?]])
        extends Node[A, Vector[B]] {
      private val sep: Node[A, ?] | Null = separator.orNull

      def run(a: A, s: State): Out[Vector[B]] = {
        val results = Vector.newBuilder[B]
        var count   = 0
        var done    = false
        while !done && count < max do {
          val start = s.offset
          val ok    = (count == 0 || (sep eq null) || !sep.run(a, s).isFailed) && {
            val b = p.run(a, s)
            !b.isFailed && { results += b.get; true }
          }
          if !ok then {
            s.offset = start
            done = true
          } else {
            count += 1
            if s.offset == start && count >= min then done = true
          }
        }
        if count < min then Out.failed else Out(results.result())
      }
    }

    /** A knot for [[recursive]], tied after construction, that grows a seed on left recursion. */
    final class Rec[A, B] extends Node[A, B] {
      var body: Node[A, B] | Null                 = null
      private[StrictParser] var info: Info | Null = null

      def run(a: A, s: State): Out[B] = {
        val start = s.offset
        val head  = s.findHead(this, a, start)
        if head ne null then {
          head.leftRecursive = true
          s.offset = head.seedEnd
          head.seed
        } else {
          val self = s.pushHead(this, a, start)
          var out  = body.nn.run(a, s)
          if self.leftRecursive && !out.isFailed then {
            self.seed = out
            self.seedEnd = s.offset
            var growing = true
            while growing do {
              s.offset = start
              val next = body.nn.run(a, s)
              if !next.isFailed && s.offset > self.seedEnd then {
                self.seed = next
                self.seedEnd = s.offset
              } else growing = false
            }
            out = self.seed
            s.offset = self.seedEnd
          }
          s.popHead()
          out
        }
      }

      override def toString: String = "Rec"
    }
  }

  import Node.*

  /** Normalizing sequential composition. Right-associates so that redexes surface at the head. */
  private def sequence[A, B, C](p: Node[A, B], q: Node[B, C]): Node[A, C] = {
    (p, q) match {
      case (Success(), _)                                 => q
      case (_, Success())                                 => p
      case (Failure(), _)                                 => Failure()
      case (Pure(f), Pure(g))                             => pure(Fn.andThen(f, g))
      case (Pure(Fn.Fanout(Fn.Id(), Fn.Id())), Zip(l, r)) => Pair(l, r)
      case (Pair(l, r), Pure(Fn.Proj1()))                 => ThenSkip(l, r)
      case (Pair(l, r), Pure(Fn.Proj2()))                 => SkipThen(l, r)
      case (Branch(l, r), Pure(Fn.Copair(f, g)))          => Merge(sequence(l, pure(f)), sequence(r, pure(g)))
      case (Choice(alternatives), Pure(_))                => choice(alternatives.map(sequence(_, q)))
      case (Seq(l, r), _)                                 => sequence(l, sequence(r, q))
      case (_, Seq(l, r))                                 =>
        sequence(p, l) match {
          case Seq(x, y) if (x eq p) && (y eq l) => Seq(p, q)
          case fused                             => sequence(fused, r)
        }
      case _ => Seq(p, q)
    }
  }

  /** Normalizing ordered choice: flattens nested choices, drops failures and alternatives that can never be reached
    * because an earlier one always succeeds.
    */
  private def choice[A, B](alternatives: List[Node[A, B]]): Node[A, B] = {
    val flat = alternatives.flatMap {
      case Choice(nested) => nested
      case Failure()      => Nil
      case other          => List(other)
    }
    val reachable = flat.indexWhere {
      case Success() | Pure(_) => true
      case _                   => false
    } match {
      case -1 => flat
      case i  => flat.take(i + 1)
    }
    reachable match {
      case Nil           => Failure()
      case single :: Nil => single
      case many          => Choice(many)
    }
  }

  // ===========================================================================
  // Primitives (smart constructors)
  // ===========================================================================

  extension [A, B](self: P[A, B])
    override def rule(label: String): P[A, B] = Rule(label, self)

  override def literal(expected: String): P[Unit, String] = Literal(expected)

  override def regex(expected: Regex): P[Unit, String] = {
    Scanner.compile(expected).fold(Pattern(expected))(Scan(expected, _))
  }

  override def pure[A, B](f: Fn[A, B]): P[A, B] = {
    f match {
      case Fn.Id() => Success()
      case _       => Pure(f)
    }
  }

  override def success[A]: P[A, A] = Success()

  override def failure[A, B]: P[A, B] = Failure()

  extension [A, B](self: P[A, B])
    override def andThen[C](other: P[B, C]): P[A, C] = sequence(self, other)

    override def zip[C, D](other: P[C, D]): P[(A, C), (B, D)] = {
      other match {
        case Success() => First(self)
        case _         => Zip(self, other)
      }
    }

    override def map[D](g: Fn[B, D]): P[A, D] = self.andThen(pure(g))

    override def mapInput[C](f: Fn[C, A]): P[C, B] = pure(f).andThen(self)

    override def branch[C, D](other: P[C, D]): P[Either[A, C], Either[B, D]] = Branch(self, other)

    override def merge[C](other: P[C, B]): P[Either[A, C], B] = Merge(self, other)

    override def or[C](other: P[A, C]): P[A, Either[B, C]] = {
      self.map(Fn.Inl[B, C]()).orElse(other.map(Fn.Inr[B, C]()))
    }

    override def orElse(other: P[A, B]): P[A, B] = choice(List(self, other))

    override def lookahead: P[A, A] = {
      self match {
        case Success() | Pure(_) => Success()
        case Lookahead(_)        => self
        case _                   => Lookahead(self)
      }
    }

    override def not: P[A, A] = {
      self match {
        case Failure() => Success()
        case _         => Not(self)
      }
    }

    override def repeated: P[A, Vector[B]] = Repeat(self, 0, Int.MaxValue, scala.None)

    override def times(n: Int): P[A, Vector[B]] = {
      require(n >= 0, "n must be non-negative")
      Repeat(self, n, n, scala.None)
    }

    override def atLeast(n: Int): P[A, Vector[B]] = {
      require(n >= 0, "n must be non-negative")
      Repeat(self, n, Int.MaxValue, scala.None)
    }

    override def separatedBy[C](separator: P[A, C]): P[A, Vector[B]] = Repeat(self, 1, Int.MaxValue, Some(separator))

  extension [A, B](self: P[A, Either[B, A]])
    override def loop: P[A, B] = Loop(self)

  override def recursive[A, B](f: P[A, B] => P[A, B]): P[A, B] = {
    val knot = Rec[A, B]()
    knot.body = f(knot)
    knot
  }

  // ===========================================================================
  // Categorical structure
  // ===========================================================================
  //
  // The same structures as ReferenceParser, implemented by the smart constructors above, so that their laws are
  // checked against the actual implementation. Equalities hold extensionally (the terms may differ in shape) and with
  // the same exceptions as for ReferenceParser: parsers are premonoidal, composition distributes over choice only on
  // one side, and loops and fixed points must be productive. In addition, left-recursive fixed points are grown from
  // a seed and break the Conway laws.

  /** Parsers form a category over `Fn`: `pure` is the unit, `success` the identity and `andThen` the composition. */
  given NodeIsPromonad: Node is Promonad {
    type On = Fn

    override val OnIsPromonad: Fn.FnIsPromonad.type = Fn.FnIsPromonad

    def unit[A, B](f: Fn[A, B]): Node[A, B] = StrictParser.pure(f)

    def multiply[A, B, C](q: Node[B, C], p: Node[A, B]): Node[A, C] = StrictParser.andThen(p)(q)

    override def identity[A]: Node[A, A] = StrictParser.success
  }

  /** Parsers are strong with respect to (`Tuple2`, `Unit`): *first*(*p*) = *p* ⊗ `success`. */
  given NodeIsStrong: Node is Strong {
    override given given_Profunctor_Self: NodeIsPromonad.type = NodeIsPromonad
    override val SelfIsProfunctor: NodeIsPromonad.type        = NodeIsPromonad
    override val OnIsMonoidal: Fn.FnIsCartesian.type          = Fn.FnIsCartesian

    def first[A, B, C](p: Node[A, B]): Node[(A, C), (B, C)] = StrictParser.zip(p)(StrictParser.success[C])

    def second[A, B, C](p: Node[A, B]): Node[(C, A), (C, B)] = StrictParser.zip(StrictParser.success[C])(p)
  }

  /** Parsers have coproducts (`Either`, `Nothing`): the injections are pure and copairing is `merge`. */
  given NodeIsCocartesian: Node is Cocartesian {
    type Z      = Nothing
    type Tensor = Either

    override val SelfIsPromonad: NodeIsPromonad.type = NodeIsPromonad

    def absurd[A]: Node[Nothing, A] = StrictParser.pure(Fn.Absurd())

    def left[A, B]: Node[A, Either[A, B]] = StrictParser.pure(Fn.Inl())

    def right[A, B]: Node[B, Either[A, B]] = StrictParser.pure(Fn.Inr())

    def sum[A, B, C](f: Node[A, C], g: Node[B, C]): Node[Either[A, B], C] = StrictParser.merge(f)(g)

    override def tensor[A, B, C, D](p: Node[A, B], q: Node[C, D]): Node[Either[A, C], Either[B, D]] = {
      StrictParser.branch(p)(q)
    }
  }

  /** Hom-sets of parsers are additive monoids under ordered choice, with `failure` as zero. */
  given NodeIsAdditiveEnriched: Node is Enriched {
    type Over = Monoid.Additive

    override val SelfIsPromonad: NodeIsPromonad.type = NodeIsPromonad

    override given HomIsV: [A, B] => (Node[A, B] is Monoid.Additive) = new Monoid.Additive {
      type Self = Node[A, B]

      def zero: Node[A, B] = StrictParser.failure

      def plus(p: Node[A, B], q: Node[A, B]): Node[A, B] = StrictParser.orElse(p)(q)
    }
  }

  /** Parsers form a restriction category: the restriction of a parser is its `lookahead`. */
  given NodeIsRestriction: Node is Restriction {
    override val SelfIsPromonad: NodeIsPromonad.type = NodeIsPromonad

    def restrict[A, B](p: Node[A, B]): Node[A, A] = StrictParser.lookahead(p)
  }

  /** Parsers have an Elgot iteration on their coproducts: the dagger is `loop`. */
  given NodeIsElgot: Node is Elgot {
    override val SelfIsCocartesian: NodeIsCocartesian.type = NodeIsCocartesian

    def dagger[A, C](p: Node[C, Either[A, C]]): Node[C, A] = StrictParser.loop(p)
  }

  /** Hom-sets of parsers have fixed points: fix is `recursive`. */
  given NodeIsFixedEnriched: Node is Enriched {
    type Over = Fixed

    override val SelfIsPromonad: NodeIsPromonad.type = NodeIsPromonad

    override given HomIsV: [A, B] => (Node[A, B] is Fixed) = new Fixed {
      type Self = Node[A, B]

      def fix(f: Node[A, B] => Node[A, B]): Node[A, B] = StrictParser.recursive(f)
    }
  }
}
