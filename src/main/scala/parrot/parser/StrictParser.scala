package parrot
package parser

import category.*

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.matching.Regex

import category.Category.Type

/** An optimizing [[ParserAlgebra]] interpreter that normalizes parsers at construction time and runs them without
  * allocating intermediate objects at runtime.
  *
  * Parsers are reified parser terms over reified pure functions. The structures on nodes are implemented by smart
  * constructors that rewrite towards a normal form, so the derived combinators collapse into specialized nodes. See
  * [[StrictParser.Node]] and [[Fn]].
  *
  * Nodes return their results unboxed and signal failure with a private sentinel value instead of an `Option`, so that
  * tracking failure allocates nothing. See [[StrictParser.Out]].
  *
  * Regular expressions in the single-character-atom fragment are precompiled. See [[Scanner]]. Other expressions fall
  * back to `scala.util.matching.Regex`.
  *
  * Nested ordered choices are flattened into a single choice node that dispatches on the next character using static
  * first-set and nullability analysis. See [[StrictParser.Info]].
  *
  * Recursion ties a knot [[StrictParser.Node.Rec]].
  *
  * This interpreter agrees with [[ReferenceParser]] on every grammar, with one extension: where a recursive parser
  * calls itself with the same semantic input at the same position, the reference fails the call, while this interpreter
  * supports left recursion by seed growing.
  *
  * @see docs/TUTORIAL.md §20.8
  */
class StrictParser
    extends ParserAlgebra(
      StrictParser.Nodes,
      Fns.Product,
      Fns.Coproduct,
      StrictParser.Zipping,
      StrictParser.Branching,
      StrictParser.Backtracking,
      StrictParser.Loops,
      StrictParser.Knots,
    ) {
  import StrictParser.*
  import StrictParser.Node.*

  def lift[A, B](f: A -> B): Fn[A, B] = {
    Fn.lift(f)
  }

  def rule[A, B](p: Node[A, B], label: String): Node[A, B] = {
    Rule(label, p)
  }

  def literal(expected: String): Node[Unit, String] = {
    Literal(expected)
  }

  def regex(expected: Regex): Node[Unit, String] = {
    Scanner.compile(expected).fold(Pattern(expected))(Scan(expected, _))
  }

  def matched[A, B](p: Node[A, B]): Node[A, (B, String)] = {
    Matched(p)
  }

  /** Runs `p` without building its result: a literal or a regular expression already returns what it consumed. */
  override def capture[A, B](p: Node[A, B]): Node[A, String] = {
    p match {
      case Literal(_) | Pattern(_)    => p.asInstanceOf[Node[A, String]]
      case Scan(expected, scanner, _) => Scan(expected, scanner).asInstanceOf[Node[A, String]]
      case _                          => Capture(discard(p))
    }
  }

  /** Running parsers: with diagnostics they mean what the reference says, and [[run]] skips the diagnostics. */
  object Semantics extends parser.Semantics(this) {
    import ReferenceParser.Input

    def denote[A, B](p: Node[A, B]): A -> Input -> (Expected, Option[(B, Input)]) = {
      a => in =>
        val state = new State(in.source, diagnostics = true, in.offset)
        val out   = p.run(a, state)
        (state.reported, out.fold(scala.None)(b => Some((b, Input(in.source, state.offset)))))
    }

    override def run[A, B](p: Node[A, B])(a: A, source: String, offset: Int = 0): Option[(B, Int)] = {
      val state = new State(source, diagnostics = false, offset)
      val out   = p.run(a, state)
      out.fold(scala.None)(b => Some((b, state.offset)))
    }
  }

  export Semantics.{diagnose, run, parse, parseAll}

  override def repeated[A, B](p: Node[A, B]): Node[A, Vector[B]] = {
    Repeat(p, 0, Int.MaxValue, scala.None)
  }

  override def times[A, B](p: Node[A, B], n: Int): Node[A, Vector[B]] = {
    require(n >= 0, "n must be non-negative")
    Repeat(p, n, n, scala.None)
  }

  override def atLeast[A, B](p: Node[A, B], n: Int): Node[A, Vector[B]] = {
    require(n >= 0, "n must be non-negative")
    Repeat(p, n, Int.MaxValue, scala.None)
  }

  override def separatedBy[A, B, C](p: Node[A, B], separator: Node[A, C]): Node[A, Vector[B]] = {
    Repeat(p, 1, Int.MaxValue, Some(discard(separator)))
  }

  override def attempt[A, B](p: Node[A, B]): Node[A, Either[B, A]] = {
    StrictParser.choice(List(sequence(p, Pure(Fn.Inl[B, A]())), Pure(Fn.Inr[B, A]())))
  }
}

object StrictParser {

  /** The unboxed result of running a node: either a value of `B` or a failure sentinel. */
  type Out[+B] = Out.Out[B]

  object Out {

    /** Unboxed representation: either a value of `B` itself, or the failure sentinel. */
    opaque type Out[+B] = B | Failed.type

    private object Failed

    /** The failed result. Private, so that no lifted function can return it as a value. */
    private[StrictParser] val failed: Out[Nothing] = Failed

    /** Wraps a successful `value` without boxing. */
    inline def apply[B](value: B): Out[B] = value

    extension [B](out: Out[B]) {

      /** True if `out` is a failure. */
      inline def isFailed: Boolean = out.asInstanceOf[AnyRef] eq Failed

      /** The value of a successful `out`. */
      private inline def get: B = out.asInstanceOf[B]

      /** Applies `f` to the value of a successful `out`. */
      inline def map[C](inline f: B -> C): Out[C] = if isFailed then failed else Out(f(get))

      /** Runs `f` on the value of a successful `out`, and fails if `out` failed. */
      inline def flatMap[C](inline f: B -> Out[C]): Out[C] = if isFailed then failed else f(get)

      /** `ifFailed` if `out` is a failure, and `f` of its value otherwise. */
      inline def fold[C](inline ifFailed: C)(inline f: B -> C): C = if isFailed then ifFailed else f(get)
    }
  }

  /** An active call of the recursive parser `rec` on `arg` at `start`, with the seed it grows if it turns out to be
    * left-recursive.
    */
  final private class Head[A, B](val rec: Node.Rec[A, B], val arg: A, val start: Int) {
    var seed: Out[B]           = Out.failed
    var seedEnd: Int           = start
    var leftRecursive: Boolean = false
  }

  /** The mutable state of a single run.
    *
    * The state contains the current position, the stack of active recursive calls, and, when `diagnostics` is set, what
    * was expected where something failed furthest.
    *
    * Without diagnostics, nothing is recorded and choices dispatch on the next character. With diagnostics, choices try
    * every alternative in order and failures are recorded exactly as [[ReferenceParser]] reports them.
    */
  final private[StrictParser] class State(val source: String, val diagnostics: Boolean, var offset: Int) {
    private var failedAt: Int              = -1
    private var expected: Set[Expectation] = Set.empty

    /** What was expected where something failed furthest. */
    def reported: Expected = {
      Expected(failedAt, expected)
    }

    /** Records, in diagnostics mode, that `expectation` failed at the current offset, and returns [[Out.failed]]. */
    def fail(expectation: Expectation): Out[Nothing] = {
      if diagnostics then {
        if offset > failedAt then {
          failedAt = offset
          expected = Set(expectation)
        } else if offset == failedAt then expected += expectation
      }
      Out.failed
    }

    /** Replaces the diagnostics, returning the previous ones. */
    def swap(next: Expected): Expected = {
      val previous = Expected(failedAt, expected)
      failedAt = next.position
      expected = next.expectations
      previous
    }

    /** The active recursive calls, whose positions are non-decreasing because nested calls never start before their
      * callers.
      */
    private lazy val heads = mutable.ArrayBuffer.empty[Head[?, ?]]

    /** The innermost active call of `rec`, if it started at `at`. */
    def findHead[A, B](rec: Node.Rec[A, B], at: Int): Option[Head[A, B]] = {
      @tailrec
      def loop(i: Int): Option[Head[A, B]] = {
        if i < 0 then scala.None
        else {
          val head = heads(i)
          if head.start != at then scala.None
          else if head.rec eq rec then Some(head.asInstanceOf[Head[A, B]])
          else loop(i - 1)
        }
      }
      loop(heads.size - 1)
    }

    /** Pushes the call of `rec` on `arg` at `at` as the innermost active call. */
    def pushHead[A, B](rec: Node.Rec[A, B], arg: A, at: Int): Head[A, B] = {
      val head = Head(rec, arg, at)
      heads += head
      head
    }

    /** Pops the innermost active call. */
    def popHead(): Unit = {
      heads.dropRightInPlace(1)
    }
  }

  /** Static first-set and nullability summary of a parser: if it succeeds where the next character is `c` (or at the
    * end of the input), then `c` belongs to `first`, or it is `nullable` and consumed nothing.
    *
    * @note `nullable` is what choice dispatch needs, and it is not "may succeed without consuming": a lookahead has
    *   the summary of its parser and never consumes. That property is [[Info.mayConsumeNothing]].
    */
  final case class Info(first: CharSet, nullable: Boolean) {

    /** Summary of an ordered choice between `this` and `that`. */
    def orElse(that: Info): Info = {
      Info(first.union(that.first), nullable || that.nullable)
    }

    /** Summary of `this` followed sequentially by `that`. */
    def andThen(that: => Info): Info = {
      if nullable then Info(first.union(that.first), that.nullable) else this
    }
  }

  object Info {
    given CanEqual[Info, Info] = CanEqual.derived

    /** Summary of a parser that never succeeds. */
    val never: Info = Info(CharSet.empty, false)

    /** Summary of a parser that never consumes input. */
    val consumesNothing: Info = Info(CharSet.empty, true)

    /** Summary of a parser that may consume anything, or nothing. */
    val unknown: Info = Info(CharSet.all, true)

    /** Computes the static summary of `node`, solving recursive knots by Kleene iteration from [[never]]. */
    def of[A, B](node: Node[A, B]): Info = {
      analyze(node, mutable.Map.empty)
    }

    /** Computes the summary of `node` under current knot approximations `env`. */
    private def analyze[A, B](node: Node[A, B], env: mutable.Map[Node.Rec[?, ?], Info]): Info = {
      import Node.*
      node match {
        case Rule(_, p)        => analyze(p, env)
        case Literal(expected) =>
          if expected.isEmpty then consumesNothing else Info(CharSet.of(expected.charAt(0)), false)
        case Scan(_, scanner, _)              => Info(scanner.first.set, scanner.first.nullable)
        case Pattern(_)                       => unknown
        case Pure(_) | _: Success[?] | Not(_) => consumesNothing
        case _: Failure[?, ?]                 => never
        case Seq(p, q)                        => analyze(p, env).andThen(analyze(q, env))
        case Zip(p, q)                        => analyze(p, env).andThen(analyze(q, env))
        case Pair(p, q)                       => analyze(p, env).andThen(analyze(q, env))
        case SkipThen(p, q)                   => analyze(p, env).andThen(analyze(q, env))
        case ThenSkip(p, q)                   => analyze(p, env).andThen(analyze(q, env))
        case Lookahead(p)                     => analyze(p, env)
        case Matched(p)                       => analyze(p, env)
        case Capture(p)                       => analyze(p, env)
        case Loop(p)                          => analyze(p, env)
        case Merge(p, q)                      => analyze(p, env).orElse(analyze(q, env))
        case Choice(alternatives)             => alternatives.map(analyze(_, env)).reduce(_.orElse(_))
        case Repeat(p, min, _, separator)     =>
          val item  = analyze(p, env)
          val after = if item.nullable then separator.fold(CharSet.empty)(analyze(_, env).first) else CharSet.empty
          Info(item.first.union(after), min == 0 || item.nullable)
        case rec: Rec[A, B] =>
          @tailrec
          def fixpoint(current: Info): Info = {
            env(rec) = current
            val next = analyze(rec.body, env)
            if next == current then next else fixpoint(next)
          }

          env.get(rec).orElse(rec.info).getOrElse {
            val solved = fixpoint(never)
            val _      = env.remove(rec)
            if env.isEmpty then rec.info = Some(solved)
            solved
          }
      }
    }

    /** True if `node` may succeed without consuming input, solving recursive knots by Kleene iteration from `false`.
      *
      * It errs towards `true`, which only keeps the guard of a recursive knot.
      */
    def mayConsumeNothing(node: Node[?, ?]): Boolean = {
      silent(node, mutable.Map.empty)
    }

    /** Computes [[mayConsumeNothing]] of `node` under current knot approximations `env`. */
    private def silent(node: Node[?, ?], env: mutable.Map[Node.Rec[?, ?], Boolean]): Boolean = {
      import Node.*
      node match {
        case Rule(_, p)                                      => silent(p, env)
        case Literal(expected)                               => expected.isEmpty
        case Scan(_, scanner, _)                             => scanner.first.nullable
        case Pattern(_)                                      => true
        case Pure(_) | _: Success[?] | Lookahead(_) | Not(_) => true
        case _: Failure[?, ?]                                => false
        case Seq(p, q)                                       => silent(p, env) && silent(q, env)
        case Zip(p, q)                                       => silent(p, env) && silent(q, env)
        case Pair(p, q)                                      => silent(p, env) && silent(q, env)
        case SkipThen(p, q)                                  => silent(p, env) && silent(q, env)
        case ThenSkip(p, q)                                  => silent(p, env) && silent(q, env)
        case Loop(p)                                         => silent(p, env)
        case Matched(p)                                      => silent(p, env)
        case Capture(p)                                      => silent(p, env)
        case Merge(p, q)                                     => silent(p, env) || silent(q, env)
        case Choice(alternatives)                            => alternatives.exists(silent(_, env))
        case Repeat(p, min, _, _)                            => min == 0 || silent(p, env)
        case rec: Rec[?, ?]                                  =>
          @tailrec
          def fixpoint(current: Boolean): Boolean = {
            env(rec) = current
            val next = silent(rec.body, env)
            if next == current then next else fixpoint(next)
          }

          env.get(rec).orElse(rec.silent).getOrElse {
            val solved = fixpoint(false)
            val _      = env.remove(rec)
            if env.isEmpty then rec.silent = Some(solved)
            solved
          }
      }
    }

    /** True if `target` can be re-entered from its body without consuming input. */
    def mayLeftRecurse(target: Node.Rec[?, ?]): Boolean = {
      def reaches(node: Node[?, ?], visited: Set[Node.Rec[?, ?]]): Boolean = {
        import Node.*
        node match {
          case Rule(_, p)                                        => reaches(p, visited)
          case Literal(_) | Scan(_, _, _) | Pattern(_) | Pure(_) => false
          case _: Success[?] | _: Failure[?, ?]                  => false
          case Lookahead(p)                                      => reaches(p, visited)
          case Not(p)                                            => reaches(p, visited)
          case Loop(p)                                           => reaches(p, visited)
          case Matched(p)                                        => reaches(p, visited)
          case Capture(p)                                        => reaches(p, visited)
          case Repeat(p, _, _, sep)                              =>
            reaches(p, visited) || (mayConsumeNothing(p) && sep.exists(reaches(_, visited)))
          case Merge(p, q)          => reaches(p, visited) || reaches(q, visited)
          case Choice(alternatives) => alternatives.exists(reaches(_, visited))
          case Seq(p, q)            => reaches(p, visited) || (mayConsumeNothing(p) && reaches(q, visited))
          case Zip(p, q)            => reaches(p, visited) || (mayConsumeNothing(p) && reaches(q, visited))
          case Pair(p, q)           => reaches(p, visited) || (mayConsumeNothing(p) && reaches(q, visited))
          case SkipThen(p, q)       => reaches(p, visited) || (mayConsumeNothing(p) && reaches(q, visited))
          case ThenSkip(p, q)       => reaches(p, visited) || (mayConsumeNothing(p) && reaches(q, visited))
          case rec: Rec[?, ?]       =>
            (rec eq target) || (!visited.contains(rec) && reaches(rec.body, visited + rec))
        }
      }
      reaches(target.body, Set(target))
    }
  }

  /** A reified parser from semantic input `A` to semantic result `B`. */
  sealed trait Node[A, B] {

    /** Executes this node on semantic input `a` and mutable parse state `s`. */
    def run(a: A, s: State): Out[B]
  }

  object Node {

    /** Names `p` as the rule `label`: where `p` fails at or before its start, it expected `label`; otherwise its
      * expectations are in the context of `label`.
      */
    final case class Rule[A, B](label: String, p: Node[A, B]) extends Node[A, B] {
      def run(a: A, s: State): Out[B] = {
        if !s.diagnostics then p.run(a, s)
        else {
          val start = s.offset
          val outer = s.swap(Expected.bottom)
          val out   = p.run(a, s)
          val inner = s.reported
          val named =
            if out.isFailed && inner.position <= start then Expected.at(start, label) else inner.tag(label)
          val _ = s.swap(outer.join(named))
          out
        }
      }
    }

    /** Consumes the exact string `expected`. */
    final case class Literal(expected: String) extends Node[Unit, String] {
      private val expectation = Expectation(s"\"$expected\"", Nil)

      def run(a: Unit, s: State): Out[String] = {
        if s.source.startsWith(expected, s.offset) then {
          s.offset += expected.length
          Out(expected)
        } else s.fail(expectation)
      }
    }

    /** Consumes a regular expression compiled to a [[Scanner]]. When `discard` is set, the matched slice is not
      * allocated because its result is ignored downstream.
      */
    final case class Scan(expected: Regex, scanner: Scanner, discard: Boolean = false) extends Node[Unit, String] {
      private val expectation = Expectation(s"/${expected.regex}/", Nil)

      def run(a: Unit, s: State): Out[String] = {
        val start = s.offset
        val end   = scanner.scan(s.source, start)
        if end < 0 then s.fail(expectation)
        else {
          s.offset = end
          if discard then Out("") else Out(s.source.slice(start, end))
        }
      }
    }

    /** Consumes a regular expression outside the [[Scanner]] fragment, matched in context ([[Scanner.matchAt]]). */
    final case class Pattern(expected: Regex) extends Node[Unit, String] {
      private val expectation = Expectation(s"/${expected.regex}/", Nil)

      def run(a: Unit, s: State): Out[String] = {
        val start = s.offset
        val end   = Scanner.matchAt(expected, s.source, start)
        if end < 0 then s.fail(expectation)
        else {
          s.offset = end
          Out(s.source.substring(start, end).nn)
        }
      }
    }

    /** Runs `p` and pairs its result with the input it consumed. */
    final case class Matched[A, B](p: Node[A, B]) extends Node[A, (B, String)] {
      def run(a: A, s: State): Out[(B, String)] = {
        val start = s.offset
        p.run(a, s).map(b => (b, s.source.slice(start, s.offset)))
      }
    }

    /** Runs `p`, whose result is not needed, and returns the input it consumed. */
    final case class Capture[A](p: Node[A, ?]) extends Node[A, String] {
      def run(a: A, s: State): Out[String] = {
        val start = s.offset
        p.run(a, s).map(_ => s.source.slice(start, s.offset))
      }
    }

    /** Applies the reified pure function `f` without consuming input. */
    final case class Pure[A, B](f: Fn[A, B]) extends Node[A, B] {
      def run(a: A, s: State): Out[B] = Out(f(a))
    }

    /** Succeeds without consuming input, returning the semantic input unchanged. */
    final case class Success[A]() extends Node[A, A] {
      def run(a: A, s: State): Out[A] = Out(a)
    }

    /** Fails immediately without consuming input, reporting nothing: the restriction zero. */
    final case class Failure[A, B]() extends Node[A, B] {
      def run(a: A, s: State): Out[B] = Out.failed
    }

    /** Sequential composition: runs `p`, then feeds its result to `q`. */
    final case class Seq[A, B, C](p: Node[A, B], q: Node[B, C]) extends Node[A, C] {
      def run(a: A, s: State): Out[C] = {
        p.run(a, s).flatMap(q.run(_, s))
      }
    }

    /** The left-to-right tensor *p* ⋉ *q*: runs `p` on the left input, then `q` on the right input, pairing their results.
      */
    final case class Zip[A, B, C, D](p: Node[A, B], q: Node[C, D]) extends Node[(A, C), (B, D)] {
      def run(ac: (A, C), s: State): Out[(B, D)] = {
        for {
          b <- p.run(ac._1, s)
          d <- q.run(ac._2, s)
        } yield (b, d)
      }
    }

    /** Runs `p` and `q` on the same semantic input, pairing their results: ⟨*p*,*q*⟩ = Δ ⨾ (*p* ⋉ *q*), where the input
      * is never duplicated into a pair.
      */
    final case class Pair[A, B, C](p: Node[A, B], q: Node[A, C]) extends Node[A, (B, C)] {
      def run(a: A, s: State): Out[(B, C)] = {
        for {
          b <- p.run(a, s)
          c <- q.run(a, s)
        } yield (b, c)
      }
    }

    /** Runs `p` then `q` on the same semantic input, keeping only the result of `q`: ⟨*p*,*q*⟩ ⨾ *π*₂, where no result
      * pair is built.
      */
    final case class SkipThen[A, B, C](p: Node[A, B], q: Node[A, C]) extends Node[A, C] {
      def run(a: A, s: State): Out[C] = {
        if p.run(a, s).isFailed then Out.failed else q.run(a, s)
      }
    }

    /** Runs `p` then `q` on the same semantic input, keeping only the result of `p`: ⟨*p*,*q*⟩ ⨾ *π*₁, where no result
      * pair is built.
      */
    final case class ThenSkip[A, B, C](p: Node[A, B], q: Node[A, C]) extends Node[A, B] {
      def run(a: A, s: State): Out[B] = {
        val b = p.run(a, s)
        if b.isFailed || q.run(a, s).isFailed then Out.failed else b
      }
    }

    /** Copairing: runs `p` on `Left` or `q` on `Right` into a common result type `C`: [*p*,*q*] = (*p* + *q*) ⨾ ∇,
      * where no intermediate tagged union is built.
      */
    final case class Merge[A, B, C](p: Node[A, C], q: Node[B, C]) extends Node[Either[A, B], C] {
      def run(ab: Either[A, B], s: State): Out[C] = ab match {
        case Left(a)  => p.run(a, s)
        case Right(b) => q.run(b, s)
      }
    }

    /** Precomputed dispatch table for each ASCII character, any non-ASCII character, and the end of input: the
      * alternatives that can succeed there, in order.
      */
    final private class Dispatch[A, B](alternatives: List[Node[A, B]]) {
      private val analyzed = alternatives.map(node => (node = node, info = Info.of(node)))

      private def select(admits: Info => Boolean): Array[Node[A, B]] = {
        analyzed.collect { case (node, info) if admits(info) => node }.toArray
      }

      val all: Array[Node[A, B]]          = alternatives.toArray
      val ascii: Array[Array[Node[A, B]]] =
        Array.tabulate(128)(c => select(i => i.nullable || i.first.contains(c.toChar)))
      val other: Array[Node[A, B]] = select(i => i.nullable || i.first.hasNonAscii)
      val end: Array[Node[A, B]]   = select(_.nullable)
    }

    /** Ordered choice between two or more alternatives, dispatching on the next character unless diagnostics are
      * recorded, which need every alternative to run.
      */
    final case class Choice[A, B](alternatives: List[Node[A, B]]) extends Node[A, B] {
      private lazy val dispatch = Dispatch(alternatives)

      def run(a: A, s: State): Out[B] = {
        val start  = s.offset
        val source = s.source
        val table  = dispatch
        val nodes  =
          if s.diagnostics then table.all
          else if start >= source.length then table.end
          else {
            val c = source.charAt(start)
            if c < 128 then table.ascii(c) else table.other
          }

        @tailrec
        def tryFrom(i: Int): Out[B] = {
          if i >= nodes.length then Out.failed
          else {
            val out = nodes(i).run(a, s)
            if !out.isFailed then out
            else {
              s.offset = start
              tryFrom(i + 1)
            }
          }
        }

        tryFrom(0)
      }
    }

    /** Runs `p` without reporting its diagnostics. */
    private def silently[A, B](p: Node[A, B], a: A, s: State): Out[B] = {
      if !s.diagnostics then p.run(a, s)
      else {
        val outer = s.swap(Expected.bottom)
        val out   = p.run(a, s)
        val _     = s.swap(outer)
        out
      }
    }

    /** Positive lookahead: succeeds iff `p` succeeds, restoring the input offset and returning `a`. Silent. */
    final case class Lookahead[A, B](p: Node[A, B]) extends Node[A, A] {
      def run(a: A, s: State): Out[A] = {
        val start = s.offset
        if silently(p, a, s).isFailed then Out.failed
        else {
          s.offset = start
          Out(a)
        }
      }
    }

    /** Negative lookahead: succeeds iff `p` fails, restoring the input offset and returning `a`. Silent. */
    final case class Not[A, B](p: Node[A, B]) extends Node[A, A] {
      def run(a: A, s: State): Out[A] = {
        val start = s.offset
        val out   = silently(p, a, s)
        s.offset = start
        if out.isFailed then Out(a) else Out.failed
      }
    }

    /** Guarded iteration: runs `p` repeatedly on `Right` results until it produces `Left`, and fails as soon as a step
      * produces `Right` without consuming input.
      */
    final case class Loop[A, B](p: Node[A, Either[B, A]]) extends Node[A, B] {
      def run(a: A, s: State): Out[B] = {
        @tailrec
        def step(cur: A): Out[B] = {
          val start = s.offset
          p.run(cur, s).flatMap {
            case Left(b)                         => Out(b)
            case Right(next) if s.offset > start => step(next)
            case Right(_)                        => Out.failed
          }
        }
        step(a)
      }
    }

    /** Runs `p` between `min` and `max` times, separated by `separator`, collecting results into a `Vector`.
      *
      * The first `min` runs are unguarded; after them, a run (with its separator) that succeeds without consuming input
      * fails the repetition silently, as guarded iteration does.
      */
    final case class Repeat[A, B](p: Node[A, B], min: Int, max: Int, separator: Option[Node[A, ?]])
        extends Node[A, Vector[B]] {
      def run(a: A, s: State): Out[Vector[B]] = {

        /** Runs the separator, if any, then `p`; restores the offset if either fails. */
        def next(): Out[B] = {
          val start = s.offset
          val sepOk = separator match {
            case Some(sep) => !sep.run(a, s).isFailed
            case _         => true
          }
          val item = if sepOk then p.run(a, s) else Out.failed
          if item.isFailed then s.offset = start
          item
        }

        @tailrec
        def loop(results: mutable.Builder[B, Vector[B]], count: Int): Out[Vector[B]] = {
          if count >= max then Out(results.result())
          else {
            val start = s.offset
            next().fold(if count >= min then Out(results.result()) else Out.failed) { item =>
              if count >= min && s.offset == start then Out.failed
              else {
                results += item
                loop(results, count + 1)
              }
            }
          }
        }

        if max == 0 then Out(Vector.empty)
        else {
          val start0 = s.offset
          p.run(a, s).fold {
            s.offset = start0
            if min == 0 then Out(Vector.empty) else Out.failed
          } { first =>
            if min == 0 && s.offset == start0 then Out.failed
            else if max == 1 then Out(Vector(first))
            else {
              val start = s.offset
              next().fold(if min <= 1 then Out(Vector(first)) else Out.failed) { second =>
                if min <= 1 && s.offset == start then Out.failed
                else {
                  val results = Vector.newBuilder[B]
                  results += first
                  results += second
                  loop(results, 2)
                }
              }
            }
          }
        }
      }
    }

    /** A recursive parser knot for [[ParserAlgebra.recursive]], tied lazily.
      *
      * A call that re-enters the knot at the position of its innermost active call fails, as guarded recursion does,
      * unless it has the same semantic input: then it is left recursion, which is solved by seed growing.
      */
    final class Rec[A, B](f: Node[A, B] -> Node[A, B]) extends Node[A, B] {
      lazy val body: Node[A, B]                         = f(this)
      private[StrictParser] var info: Option[Info]      = scala.None
      private[StrictParser] var silent: Option[Boolean] = scala.None
      private lazy val mayLeftRecurse: Boolean          = Info.mayLeftRecurse(this)

      private given CanEqual[A, A] = CanEqual.derived

      def run(a: A, s: State): Out[B] = {
        if !mayLeftRecurse then body.run(a, s)
        else {
          val start = s.offset
          s.findHead(this, start) match {
            case Some(head) if head.arg == a =>
              head.leftRecursive = true
              s.offset = head.seedEnd
              head.seed
            case Some(_) =>
              Out.failed
            case scala.None =>
              val self = s.pushHead(this, a, start)
              val out  = body.run(a, s)
              val res  =
                if self.leftRecursive && !out.isFailed then grow(a, s, start, self, out)
                else out
              s.popHead()
              res
          }
        }
      }

      @tailrec
      private def grow(a: A, s: State, start: Int, self: Head[A, B], seed: Out[B]): Out[B] = {
        self.seed = seed
        self.seedEnd = s.offset
        s.offset = start
        val next = body.run(a, s)
        if !next.isFailed && s.offset > self.seedEnd then grow(a, s, start, self, next)
        else {
          s.offset = self.seedEnd
          self.seed
        }
      }

      override def toString: String = "Rec"
    }
  }

  import Node.*

  /** Normalizing sequential composition, right-associated so that redexes surface at the head.
    *
    * Pure post-processing distributes over copairing and ordered choice:
    *   - (*p* + *q*) ⨾ [*f*,*g*] becomes [*p* ⨾ *f*,*q* ⨾ *g*]: no intermediate tagged union is built
    *   - (*p* ⊳ *q*) ⨾ *f* becomes (*p* ⨾ *f*) ⊳ (*q* ⨾ *f*)
    */
  private def sequence[A, B, C](p: Node[A, B], q: Node[B, C]): Node[A, C] = {
    // `Seq(Lookahead(p), p)` must not become `p`: with diagnostics R1 is an inequation, since the lookahead is silent
    // where `p` fails ([[ParserAlgebra.ParserLaws.lookaheadIdentity]]).
    (p, q) match {
      case (_: Success[?], _)                                     => q
      case (_, _: Success[?])                                     => p
      case (_: Failure[?, ?], _)                                  => Failure()
      case (Pure(f), Pure(g))                                     => Nodes.unit(Fn.andThen(f, g))
      case (Pure(_: Fn.Inl[?, ?]), Merge(l, _))                   => l
      case (Pure(_: Fn.Inr[?, ?]), Merge(_, r))                   => r
      case (Zip(l, _: Success[?]), Zip(_: Success[?], r))         => Zip(l, r)
      case (Pure(Fn.Fanout(_: Fn.Id[?], _: Fn.Id[?])), Zip(l, r)) => Pair(l, r)
      case (Pair(l, r), Pure(_: Fn.Proj1[?, ?]))                  => ThenSkip(l, discard(r))
      case (Pair(l, r), Pure(_: Fn.Proj2[?, ?]))                  => SkipThen(discard(l), r)
      case (Merge(l, r), Pure(_) | Merge(_, _))                   => Merge(sequence(l, q), sequence(r, q))
      case (Choice(alternatives), Pure(_))                        => choice(alternatives.map(sequence(_, q)))
      case (Seq(l, r), _)                                         => sequence(l, sequence(r, q))
      case (_, Seq(l, r))                                         =>
        sequence(p, l) match {
          case Seq(x, y) if (x eq p) && (y eq l) => Seq(p, q)
          case fused                             => sequence(fused, r)
        }
      case _ => Seq(p, q)
    }
  }

  /** Strips pure post-processing and string allocation from `node` when its semantic result is discarded. */
  private def discard[A, B](node: Node[A, B]): Node[A, ?] = {
    node match {
      case Pure(_)               => Success()
      case Scan(expected, sc, _) => Scan(expected, sc, discard = true)
      case Seq(p, Pure(_))       => discard(p)
      case Seq(p, q)             => Seq(p, discard(q))
      case Pair(p, q)            => SkipThen(discard(p), discard(q))
      case SkipThen(p, q)        => SkipThen(p, discard(q))
      case ThenSkip(p, q)        => ThenSkip(discard(p), q)
      case Choice(alternatives)  => choice(alternatives.map(a => discard(a).asInstanceOf[Node[A, Any]]))
      case Rule(label, p)        => Rule(label, discard(p))
      case Matched(p)            => discard(p)
      case Capture(p)            => p
      case _                     => node
    }
  }

  /** Normalizing ordered choice: flattens nested choices, drops failures, and prunes unreachable alternatives after a
    * total parser.
    */
  private def choice[A, B](alternatives: List[Node[A, B]]): Node[A, B] = {
    val flat = alternatives.flatMap {
      case Choice(nested)   => nested
      case _: Failure[?, ?] => Nil
      case other            => List(other)
    }
    val (before, fromTotal) = flat.span {
      case _: Success[?] | Pure(_) => false
      case _                       => true
    }
    (before ::: fromTotal.take(1)) match {
      case Nil           => Failure()
      case single :: Nil => single
      case many          => Choice(many)
    }
  }

  /** Nodes form a promonad over [[Fns]], with `Success` as identity and normalizing sequential composition. */
  object Nodes extends Promonad(Fns) {
    type Self = Node

    def unit[A: Type, B: Type](f: Fn[A, B]): Node[A, B] = {
      f match {
        case _: Fn.Id[?] => Success()
        case _           => Pure(f)
      }
    }

    def multiply[A: Type, B: Type, C: Type](q: Node[B, C], p: Node[A, B]): Node[A, C] = {
      sequence(p, q)
    }
  }

  /** Nodes run side by side on pairs: `Zip`. */
  object Zipping extends Bistrong(Nodes, Fns.Product) {

    def left[A: Type, B: Type, C: Type]: Node[A, B] -> Node[(C, A), (C, B)] = {
      case _: Success[?] => Success()
      case p             => Zip(Success(), p)
    }

    override def right[A: Type, B: Type, C: Type]: Node[A, B] -> Node[(A, C), (B, C)] = {
      case _: Success[?] => Success()
      case p             => Zip(p, Success())
    }
  }

  /** Nodes run on one side of a tagged union: `Merge` with pure injections. */
  object Branching extends Bistrong(Nodes, Fns.Coproduct) {

    def left[A: Type, B: Type, C: Type]: Node[A, B] -> Node[Either[C, A], Either[C, B]] = {
      p => Merge(Pure(Fn.Inl[C, B]()), sequence(p, Pure(Fn.Inr[C, B]())))
    }

    override def right[A: Type, B: Type, C: Type]: Node[A, B] -> Node[Either[A, C], Either[B, C]] = {
      p => Merge(sequence(p, Pure(Fn.Inl[B, C]())), Pure(Fn.Inr[B, C]()))
    }
  }

  /** Failure, lookahead, negation, attempt and ordered choice: `Failure`, `Lookahead`, `Not` and `Choice`. */
  object Backtracking extends Classical(Nodes.arrows) {

    def restrict[A: Type, B: Type](p: Node[A, B]): Node[A, A] = {
      discard(p) match {
        case _: Success[?] | Pure(_) => Success()
        case Lookahead(inner)        => Lookahead(inner)
        case discarded               => Lookahead(discarded)
      }
    }

    def zero[A: Type, B: Type]: Node[A, B] = {
      Failure()
    }

    def complement[A: Type, B: Type](p: Node[A, B]): Node[A, A] = {
      discard(p) match {
        case _: Failure[?, ?] => Success()
        case discarded        => Not(discarded)
      }
    }

    def orElse[A: Type, B: Type](p: Node[A, B], q: Node[A, B]): Node[A, B] = {
      choice(List(p, q))
    }
  }

  /** Guarded iteration: `Loop`. */
  object Loops extends GuardedIteration(Branching) {

    def iterate[A: Type, X: Type](p: Node[X, Either[A, X]]): Node[X, A] = {
      Loop(p)
    }
  }

  /** Guarded recursion, with left recursion solved by seed growing: `Rec`. */
  object Knots extends GuardedRecursion(Nodes) {

    def fix[A: Type, B: Type](f: Node[A, B] -> Node[A, B]): Node[A, B] = {
      val knot = Rec(f)
      val _    = knot.body
      knot
    }

    /** One [[Rec]] knot per arrow of the family, each with its own record of active calls, so that seed growing handles
      * mutual left recursion; `f` is applied once.
      */
    override def fixFamily[A: Type, B: Type](n: Int)(f: (Int -> Node[A, B]) -> Int -> Node[A, B]): Int -> Node[A, B] = {
      lazy val solved: Int -> Node[A, B] = f(i => knots(i))
      lazy val knots: Vector[Rec[A, B]]  = Vector.tabulate(n)(i => Rec[A, B](_ => solved(i)))
      for knot <- knots do {
        val _ = knot.body
      }
      i => knots(i)
    }
  }
}
