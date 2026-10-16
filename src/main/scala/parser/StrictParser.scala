package parrot
package parser

import category.*

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.control.NoStackTrace
import scala.util.matching.Regex
import scala.util.{Try, Failure as TryFailure, Success as TrySuccess}

/** An optimizing [[ParserAlgebra]] interpreter that normalizes parsers at construction time and runs them without
  * allocating intermediate structure.
  *
  * Parsers are reified terms ([[Node]]) over reified pure functions ([[Fn]]). The categorical structures on [[Node]]
  * are implemented as smart constructors that rewrite their arguments towards a normal form, so the standard mixins
  * collapse into specialized nodes:
  *   - `p.pair(q)` = `p.zip(q).mapInput(Δ)` becomes `Pair(p, q)`: the input is never duplicated into a tuple
  *   - `p.skipThen(q)` = `Pair(p, q).map(π₂)` becomes `SkipThen(p, q)`: no result tuple is built
  *   - `p.branch(q).map([f, g])` becomes `Merge(p.map(f), q.map(g))`: no intermediate `Either` is built
  *   - `(p orElse q).map(f)` becomes `p.map(f) orElse q.map(f)`, so `(p or q).map([f, g])` becomes
  *     `p.map(f) orElse q.map(g)`: again no intermediate `Either` is built
  *
  * Regular expressions in the single-character-atom fragment are compiled to a [[Scanner]]; other expressions fall back
  * to [[Regex.findPrefixOf]]. Nested ordered choices are flattened into a single [[Node.Choice]] that dispatches on the
  * next character using static first-set and nullability analysis ([[Info]]). `recursive` ties a knot ([[Node.Rec]])
  * and supports left recursion by seed growing.
  */
trait StrictParser extends ParserAlgebra.CanonicalParser {

  type On          = Fn
  type Self        = Node
  type Empty       = Unit
  type Pair        = Tuple2
  type None        = Nothing
  type Alternative = Either
  type Many        = Vector

  override val OnIsCartesian: Fn.FnIsCartesian.type     = ConcatenationOnCartesian
  override val OnIsCocartesian: Fn.FnIsCocartesian.type = ConcatenationOnCocartesian

  override given ConcatenationOnCartesian: Fn.FnIsCartesian.type       = Fn.FnIsCartesian
  override given ConcatenationOnCocartesian: Fn.FnIsCocartesian.type   = Fn.FnIsCocartesian
  override given SequencingPromonad: Node.NodeIsPromonad.type          = Node.NodeIsPromonad
  override given ZippingStrong: Node.NodeIsStrong.type                 = Node.NodeIsStrong
  override given AlternationEnriched: Node.NodeIsAdditiveEnriched.type = Node.NodeIsAdditiveEnriched
  override given LookaheadRestriction: Node.NodeIsRestriction.type     = Node.NodeIsRestriction
  override given IterationElgot: Node.NodeIsElgot.type                 = Node.NodeIsElgot
  override given BranchingCocartesian: Node.NodeIsCocartesian.type     = Node.NodeIsCocartesian
  override given RecursionEnriched: Node.NodeIsFixedEnriched.type      = Node.NodeIsFixedEnriched

  /** Parse error at `offset` with `expected` message. */
  final case class ParseError(offset: Int, expected: String) extends Exception with NoStackTrace {
    override def getMessage: String = s"expected $expected at position $offset"
  }

  /** The unboxed result of running a node: either a value of `B` or a failure sentinel. */
  type Out[+B] = Out.Out[B]

  object Out {

    /** Unboxed representation: either a value of `B` itself, or the failure sentinel. */
    opaque type Out[+B] = Any

    private object Failed

    /** The failed result. */
    val failed: Out[Nothing] = Failed

    /** Wraps a successful `value` without boxing. */
    inline def apply[B](value: B): Out[B] = value

    extension [B](out: Out[B])
      /** True if `out` is a failure. */
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

  /** The mutable state of a single run: the current position, the furthest failure, and the stack of active recursive
    * calls.
    */
  final class State(val source: String) {
    var offset: Int      = 0
    var failedAt: Int    = -1
    var expected: String = ""

    /** Records a failure expecting `label` at the current offset and returns [[Out.failed]]. */
    def fail(label: String): Out[Nothing] = {
      if offset > failedAt then {
        failedAt = offset
        expected = label
      }
      Out.failed
    }

    /** The active recursive calls, whose positions are non-decreasing because nested calls never start before their
      * callers.
      */
    private lazy val heads = mutable.ArrayBuffer.empty[Head[?, ?]]

    /** The active call of `rec` on `arg` at position `at`, if any. */
    private[StrictParser] def findHead[A, B](rec: Node.Rec[A, B], arg: A, at: Int): Option[Head[A, B]] = {
      @tailrec
      def loop(i: Int): Option[Head[A, B]] = {
        if i < 0 then scala.None
        else {
          val head = heads(i)
          if head.start != at then scala.None
          else if (head.rec eq rec) && head.arg.equals(arg) then Some(head.asInstanceOf[Head[A, B]])
          else loop(i - 1)
        }
      }
      loop(heads.size - 1)
    }

    private[StrictParser] def pushHead[A, B](rec: Node.Rec[A, B], arg: A, at: Int): Head[A, B] = {
      val head = Head(rec, arg, at)
      heads += head
      head
    }

    private[StrictParser] def popHead(): Unit = {
      heads.dropRightInPlace(1)
    }
  }

  extension [B](self: P[Unit, B])
    /** Runs `self` on a prefix of `source`. */
    def parse(source: String): Try[(result: B, offset: Int)] = {
      val state = State(source)
      val out   = self.run((), state)
      if out.isFailed then TryFailure(ParseError(state.failedAt, state.expected))
      else TrySuccess((result = out.get, offset = state.offset))
    }

    /** Runs `self` on the whole of `source`. */
    def parseAll(source: String): Try[(result: B, offset: Int)] = {
      self.parse(source).flatMap { (result, offset) =>
        if offset == source.length then TrySuccess((result = result, offset = offset))
        else TryFailure(ParseError(offset, "end of input"))
      }
    }

  /** Static first-set and nullability summary of a parser: if it succeeds where the next character is `c` (or at the
    * end of the input), then it is `nullable` or `c` belongs to `first`.
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

    /** Summary of a parser that may succeed without consuming input. */
    val unknown: Info = Info(CharSet.empty, true)

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
          if expected.isEmpty then unknown else Info(CharSet.of(expected.charAt(0)), false)
        case Scan(_, scanner, _)                       => Info(scanner.first.set, scanner.first.nullable)
        case Pattern(_) | Pure(_) | Success() | Not(_) => unknown
        case Failure()                                 => never
        case Seq(p, q)                                 => analyze(p, env).andThen(analyze(q, env))
        case Zip(p, q)                                 => analyze(p, env).andThen(analyze(q, env))
        case Pair(p, q)                                => analyze(p, env).andThen(analyze(q, env))
        case SkipThen(p, q)                            => analyze(p, env).andThen(analyze(q, env))
        case ThenSkip(p, q)                            => analyze(p, env).andThen(analyze(q, env))
        case Lookahead(p)                              => analyze(p, env)
        case Loop(p)                                   => analyze(p, env)
        case Merge(p, q)                               => analyze(p, env).orElse(analyze(q, env))
        case Choice(alternatives)                      => alternatives.map(analyze(_, env)).reduce(_.orElse(_))
        case Repeat(p, min, _, _)                      =>
          val item = analyze(p, env)
          if min == 0 || item.nullable then unknown else item
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

    /** True if `target` can be re-entered from its body without consuming input. */
    def mayLeftRecurse(target: Node.Rec[?, ?]): Boolean = {
      def reaches(node: Node[?, ?], visited: Set[Node.Rec[?, ?]]): Boolean = {
        import Node.*
        node match {
          case Rule(_, p)                                                                => reaches(p, visited)
          case Literal(_) | Scan(_, _, _) | Pattern(_) | Pure(_) | Success() | Failure() => false
          case Lookahead(p)                                                              => reaches(p, visited)
          case Not(p)                                                                    => reaches(p, visited)
          case Loop(p)                                                                   => reaches(p, visited)
          case Repeat(p, _, _, sep)                                                      =>
            reaches(p, visited) || (of(p).nullable && sep.exists(reaches(_, visited)))
          case Merge(p, q)          => reaches(p, visited) || reaches(q, visited)
          case Choice(alternatives) => alternatives.exists(reaches(_, visited))
          case Seq(p, q)            => reaches(p, visited) || (of(p).nullable && reaches(q, visited))
          case Zip(p, q)            => reaches(p, visited) || (of(p).nullable && reaches(q, visited))
          case Pair(p, q)           => reaches(p, visited) || (of(p).nullable && reaches(q, visited))
          case SkipThen(p, q)       => reaches(p, visited) || (of(p).nullable && reaches(q, visited))
          case ThenSkip(p, q)       => reaches(p, visited) || (of(p).nullable && reaches(q, visited))
          case rec: Rec[?, ?]       =>
            (rec eq target) || (!visited.contains(rec) && reaches(rec.body, visited + rec))
        }
      }
      reaches(target.body, Set(target))
    }

    /** The expectation message of the first failure that `node` reports when it fails without consuming input. */
    def label[A, B](node: Node[A, B], visited: Set[Node.Rec[?, ?]] = Set.empty): Option[String] = {
      import Node.*
      node match {
        case Rule(label, _)                           => Some(label)
        case l: Literal                               => Option.when(l.expected.nonEmpty)(l.label)
        case s: Scan                                  => Some(s.label)
        case p: Pattern                               => Some(p.label)
        case Failure()                                => Some("failure")
        case Not(p)                                   => label(p, visited).orElse(Some("not"))
        case Seq(p, q)                                => label(p, visited).orElse(label(q, visited))
        case Pair(p, q)                               => label(p, visited).orElse(label(q, visited))
        case SkipThen(p, q)                           => label(p, visited).orElse(label(q, visited))
        case ThenSkip(p, q)                           => label(p, visited).orElse(label(q, visited))
        case Zip(p, q)                                => label(p, visited).orElse(label(q, visited))
        case Lookahead(p)                             => label(p, visited)
        case Loop(p)                                  => label(p, visited)
        case Repeat(p, _, _, _)                       => label(p, visited)
        case Choice(alternatives)                     => alternatives.iterator.flatMap(label(_, visited)).nextOption()
        case rec: Rec[A, B] if !visited.contains(rec) => label(rec.body, visited + rec)
        case _                                        => scala.None
      }
    }
  }

  /** A reified parser from semantic input `A` to semantic result `B`. */
  sealed trait Node[A, B] {

    /** Executes this node on semantic input `a` and mutable parse state `s`. */
    def run(a: A, s: State): Out[B]
  }

  object Node {

    /** Labels `p` with rule name `label` for failure diagnostics at the starting offset. */
    final case class Rule[A, B](label: String, p: Node[A, B]) extends Node[A, B] {
      def run(a: A, s: State): Out[B] = {
        val start = s.offset
        val out   = p.run(a, s)
        if out.isFailed && s.failedAt == start then s.expected = label
        out
      }
    }

    /** Consumes the exact string `expected`. */
    final case class Literal(expected: String) extends Node[Unit, String] {
      private[StrictParser] val label: String = s"\"$expected\""

      def run(a: Unit, s: State): Out[String] = {
        if s.source.startsWith(expected, s.offset) then {
          s.offset += expected.length
          Out(expected)
        } else s.fail(label)
      }
    }

    /** Consumes a regular expression compiled to a [[Scanner]]. When `discard` is set, the matched slice is not
      * allocated because its result is ignored downstream.
      */
    final case class Scan(expected: Regex, scanner: Scanner, discard: Boolean = false) extends Node[Unit, String] {
      private[StrictParser] val label: String = s"/${expected.regex}/"

      def run(a: Unit, s: State): Out[String] = {
        val start = s.offset
        val end   = scanner.scan(s.source, start)
        if end < 0 then s.fail(label)
        else {
          s.offset = end
          if discard then Out("") else Out(s.source.slice(start, end))
        }
      }
    }

    /** Consumes a regular expression matched with [[Regex.findPrefixOf]]. */
    final case class Pattern(expected: Regex) extends Node[Unit, String] {
      private[StrictParser] val label: String = s"/${expected.regex}/"

      def run(a: Unit, s: State): Out[String] = {
        expected.findPrefixOf(s.source.subSequence(s.offset, s.source.length)) match {
          case Some(matched) =>
            s.offset += matched.length
            Out(matched)
          case scala.None =>
            s.fail(label)
        }
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

    /** Fails immediately without consuming input. */
    final case class Failure[A, B]() extends Node[A, B] {
      def run(a: A, s: State): Out[B] = s.fail("failure")
    }

    /** Sequential composition: runs `p`, then feeds its result to `q`. */
    final case class Seq[A, B, C](p: Node[A, B], q: Node[B, C]) extends Node[A, C] {
      def run(a: A, s: State): Out[C] = {
        val b = p.run(a, s)
        if b.isFailed then Out.failed else q.run(b.get, s)
      }
    }

    /** Monoidal product: runs `p` on the left input and `q` on the right input, pairing their results. */
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

    /** Runs `p` and `q` on the same semantic input, pairing their results. */
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

    /** Runs `p` then `q` on the same semantic input, keeping only the result of `q`. */
    final case class SkipThen[A, B, C](p: Node[A, B], q: Node[A, C]) extends Node[A, C] {
      def run(a: A, s: State): Out[C] = {
        if p.run(a, s).isFailed then Out.failed else q.run(a, s)
      }
    }

    /** Runs `p` then `q` on the same semantic input, keeping only the result of `p`. */
    final case class ThenSkip[A, B, C](p: Node[A, B], q: Node[A, C]) extends Node[A, B] {
      def run(a: A, s: State): Out[B] = {
        val b = p.run(a, s)
        if b.isFailed || q.run(a, s).isFailed then Out.failed else b
      }
    }

    /** Copairing: runs `p` on `Left` or `q` on `Right` into a common result type `C`. */
    final case class Merge[A, B, C](p: Node[A, C], q: Node[B, C]) extends Node[Either[A, B], C] {
      def run(ab: Either[A, B], s: State): Out[C] = ab match {
        case Left(a)  => p.run(a, s)
        case Right(b) => q.run(b, s)
      }
    }

    /** The alternatives to try, in order, for one class of next characters. `skipsFirst` is set if the first
      * alternative is not among them, so that its failure is reported as the reference interpreter would.
      */
    final private case class Candidates[A, B](nodes: Array[Node[A, B]], skipsFirst: Boolean)

    /** Precomputed dispatch table for each ASCII character, any non-ASCII character, and the end of input. */
    final private class Dispatch[A, B](alternatives: List[Node[A, B]]) {
      private val analyzed = alternatives.map(node => (node = node, info = Info.of(node)))
      val label: String    = alternatives.headOption.flatMap(Info.label(_)).getOrElse("failure")

      private def select(admits: Info => Boolean): Candidates[A, B] = {
        val nodes      = analyzed.collect { case (node, info) if admits(info) => node }.toArray
        val skipsFirst = analyzed.headOption.exists((_, info) => !admits(info))
        Candidates(nodes, skipsFirst)
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
        val nodes = candidates.nodes

        @tailrec
        def tryFrom(i: Int): Out[B] = {
          if i >= nodes.length then {
            if candidates.skipsFirst && s.failedAt <= start then {
              s.failedAt = start
              s.expected = table.label
            }
            Out.failed
          } else {
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

    /** Positive lookahead: succeeds iff `p` succeeds, restoring the input offset and returning `a`. */
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

    /** Negative lookahead: succeeds iff `p` fails, restoring the input offset and returning `a`. */
    final case class Not[A, B](p: Node[A, B]) extends Node[A, A] {
      def run(a: A, s: State): Out[A] = {
        val start = s.offset
        val out   = p.run(a, s)
        s.offset = start
        if out.isFailed then Out(a) else s.fail("not")
      }
    }

    /** Elgot iteration: runs `p` repeatedly on `Right` results until it produces `Left`. */
    final case class Loop[A, B](p: Node[A, Either[B, A]]) extends Node[A, B] {
      def run(a: A, s: State): Out[B] = {
        @tailrec
        def step(cur: A): Out[B] = {
          val out = p.run(cur, s)
          if out.isFailed then Out.failed
          else
            out.get match {
              case Left(b)     => Out(b)
              case Right(next) => step(next)
            }
        }
        step(a)
      }
    }

    /** Runs `p` between `min` and `max` times, separated by `separator`, collecting results into a `Vector`.
      *
      * Stops early when an iteration consumes no input once `min` elements have been collected.
      */
    final case class Repeat[A, B](p: Node[A, B], min: Int, max: Int, separator: Option[Node[A, ?]])
        extends Node[A, Vector[B]] {
      def run(a: A, s: State): Out[Vector[B]] = {
        @tailrec
        def loop(results: mutable.Builder[B, Vector[B]], count: Int): Int = {
          if count >= max then count
          else {
            val start = s.offset
            val sepOk = separator match {
              case Some(sep) => !sep.run(a, s).isFailed
              case _         => true
            }
            val item = if sepOk then p.run(a, s) else Out.failed
            if item.isFailed then {
              s.offset = start
              count
            } else {
              results += item.get
              val next = count + 1
              if s.offset == start && next >= min then next
              else loop(results, next)
            }
          }
        }

        if max == 0 then Out(Vector.empty)
        else {
          val start0 = s.offset
          val first  = p.run(a, s)
          if first.isFailed then {
            s.offset = start0
            if min == 0 then Out(Vector.empty) else Out.failed
          } else if max == 1 || (s.offset == start0 && min <= 1) then {
            Out(Vector(first.get))
          } else {
            val start1 = s.offset
            val sepOk  = separator match {
              case Some(sep) => !sep.run(a, s).isFailed
              case _         => true
            }
            val second = if sepOk then p.run(a, s) else Out.failed
            if second.isFailed then {
              s.offset = start1
              if min <= 1 then Out(Vector(first.get)) else Out.failed
            } else {
              val results = Vector.newBuilder[B]
              results += first.get
              results += second.get
              val total =
                if s.offset == start1 && min <= 2 then 2
                else loop(results, 2)
              if total < min then Out.failed else Out(results.result())
            }
          }
        }
      }
    }

    /** A recursive parser knot for [[recursive]], tied lazily and supporting left recursion by seed growing. */
    final class Rec[A, B](f: Node[A, B] => Node[A, B]) extends Node[A, B] {
      lazy val body: Node[A, B]                    = f(this)
      private[StrictParser] var info: Option[Info] = scala.None
      private lazy val mayLeftRecurse: Boolean     = Info.mayLeftRecurse(this)

      def run(a: A, s: State): Out[B] = {
        if !mayLeftRecurse then body.run(a, s)
        else {
          val start = s.offset
          s.findHead(this, a, start) match {
            case Some(head) =>
              head.leftRecursive = true
              s.offset = head.seedEnd
              head.seed
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

    /** `Node` is a promonad on `Fn`, with `Success` as identity and normalizing sequential composition as
      * multiplication.
      */
    given NodeIsPromonad: Node is Promonad {
      type On = Fn

      override given ProfunctorOnPromonad: Fn.FnIsPromonad.type = Fn.FnIsPromonad
      override val OnIsPromonad: Fn.FnIsPromonad.type           = Fn.FnIsPromonad

      def unit[A, B](f: Fn[A, B]): Node[A, B] = {
        f match {
          case Fn.Id() => Success()
          case _       => Pure(f)
        }
      }

      def multiply[A, B, C](q: Node[B, C], p: Node[A, B]): Node[A, C] = {
        sequence(p, q)
      }

      override def identity[A]: Node[A, A] = {
        Success()
      }

      override def lmap[A, B, C](f: Fn[C, A])(p: Node[A, B]): Node[C, B] = {
        sequence(unit(f), p)
      }

      override def rmap[A, B, D](g: Fn[B, D])(p: Node[A, B]): Node[A, D] = {
        sequence(p, unit(g))
      }
    }

    /** `Node` is cartesian strong on `Fn` with respect to (`Tuple2`, `Unit`). */
    given NodeIsStrong: Node is Strong {
      override given StrongProfunctor: NodeIsPromonad.type = NodeIsPromonad
      override val SelfIsProfunctor: NodeIsPromonad.type   = NodeIsPromonad
      override val OnIsMonoidal: Fn.FnIsCartesian.type     = Fn.FnIsCartesian

      def first[A, B, C](p: Node[A, B]): Node[(A, C), (B, C)] = {
        p match {
          case Success() => Success()
          case _         => Zip(p, Success())
        }
      }

      def second[A, B, C](p: Node[A, B]): Node[(C, A), (C, B)] = {
        p match {
          case Success() => Success()
          case _         => Zip(Success(), p)
        }
      }
    }

    /** `Node` is cocartesian under (`Either`, `Nothing`) with pure injections and `Merge` as copairing. */
    given NodeIsCocartesian: Node is Cocartesian {
      type Z      = Nothing
      type Tensor = Either

      override given CocartesianPromonad: NodeIsPromonad.type = NodeIsPromonad
      override val SelfIsPromonad: NodeIsPromonad.type        = NodeIsPromonad

      def absurd[A]: Node[Nothing, A] = {
        Pure(Fn.Absurd())
      }

      def left[A, B]: Node[A, Either[A, B]] = {
        Pure(Fn.Inl())
      }

      def right[A, B]: Node[B, Either[A, B]] = {
        Pure(Fn.Inr())
      }

      def sum[A, B, C](f: Node[A, C], g: Node[B, C]): Node[Either[A, B], C] = {
        Merge(f, g)
      }
    }

    /** Hom-sets of `Node` are additive monoids under normalizing ordered choice, with `Failure` as zero. */
    given NodeIsAdditiveEnriched: Node is Enriched {
      type Over = Monoid.Additive

      override given EnrichedPromonad: NodeIsPromonad.type = NodeIsPromonad
      override val SelfIsPromonad: NodeIsPromonad.type     = NodeIsPromonad

      override given HomIsV: [A, B] => (Node[A, B] is Monoid.Additive) = new Monoid.Additive {
        type Self = Node[A, B]

        def zero: Node[A, B] = {
          Failure()
        }

        def plus(p: Node[A, B], q: Node[A, B]): Node[A, B] = {
          choice(List(p, q))
        }
      }
    }

    /** `Node` is a restriction promonad with `Lookahead` as restriction. */
    given NodeIsRestriction: Node is Restriction {
      override given RestrictionPromonad: NodeIsPromonad.type = NodeIsPromonad
      override val SelfIsPromonad: NodeIsPromonad.type        = NodeIsPromonad

      def restrict[A, B](p: Node[A, B]): Node[A, A] = {
        discard(p) match {
          case Success() | Pure(_) => Success()
          case Lookahead(inner)    => Lookahead(inner)
          case discarded           => Lookahead(discarded)
        }
      }
    }

    /** `Node` is an Elgot promonad with `Loop` as iteration. */
    given NodeIsElgot: Node is Elgot {
      override given ElgotCocartesian: NodeIsCocartesian.type = NodeIsCocartesian
      override val SelfIsCocartesian: NodeIsCocartesian.type  = NodeIsCocartesian

      def dagger[A, C](p: Node[C, Either[A, C]]): Node[C, A] = {
        Loop(p)
      }
    }

    /** Hom-sets of `Node` are enriched over `Fixed` via `Rec`. */
    given NodeIsFixedEnriched: Node is Enriched {
      type Over = Fixed.in[Function, Unit, LazyTuple2, Function]

      override given EnrichedPromonad: NodeIsPromonad.type = NodeIsPromonad
      override val SelfIsPromonad: NodeIsPromonad.type     = NodeIsPromonad

      override given HomIsV: [A, B] => (Node[A, B] is Fixed.in[Function, Unit, LazyTuple2, Function]) =
        new Fixed {
          type Self = Node[A, B]
          type In   = Function
          type Exp  = Function

          override given FixedInCartesian: Cartesian.FunctionIsLazyCartesian.type = Cartesian.FunctionIsLazyCartesian
          override given FixedInClosed: Closed.FunctionIsLazyClosed.type          = Closed.FunctionIsLazyClosed
          override val InIsCartesian: Cartesian.FunctionIsLazyCartesian.type      = Cartesian.FunctionIsLazyCartesian
          override val InIsClosed: Closed.FunctionIsLazyClosed.type               = Closed.FunctionIsLazyClosed

          import InIsCartesian.SelfIsPromonad.~>
          import InIsClosed.^

          def fix: (F ^ F) ~> F = { f =>
            val knot = Rec(f)
            val _    = knot.body
            knot
          }
        }
    }
  }

  import Node.*

  val NodeIsPromonad: Node.NodeIsPromonad.type                 = Node.NodeIsPromonad
  val NodeIsStrong: Node.NodeIsStrong.type                     = Node.NodeIsStrong
  val NodeIsCocartesian: Node.NodeIsCocartesian.type           = Node.NodeIsCocartesian
  val NodeIsAdditiveEnriched: Node.NodeIsAdditiveEnriched.type = Node.NodeIsAdditiveEnriched
  val NodeIsRestriction: Node.NodeIsRestriction.type           = Node.NodeIsRestriction
  val NodeIsElgot: Node.NodeIsElgot.type                       = Node.NodeIsElgot
  val NodeIsFixedEnriched: Node.NodeIsFixedEnriched.type       = Node.NodeIsFixedEnriched

  /** Normalizing sequential composition, right-associated so that redexes surface at the head. */
  private def sequence[A, B, C](p: Node[A, B], q: Node[B, C]): Node[A, C] = {
    (p, q) match {
      case (Success(), _)                                 => q
      case (_, Success())                                 => p
      case (Failure(), _)                                 => Failure()
      case (Pure(f), Pure(g))                             => NodeIsPromonad.unit(Fn.andThen(f, g))
      case (Zip(l, Success()), Zip(Success(), r))         => Zip(l, r)
      case (Pure(Fn.Fanout(Fn.Id(), Fn.Id())), Zip(l, r)) => Pair(l, r)
      case (Pair(l, r), Pure(Fn.Proj1()))                 => ThenSkip(l, discard(r))
      case (Pair(l, r), Pure(Fn.Proj2()))                 => SkipThen(discard(l), r)
      case (Merge(l, r), Pure(_))                         => Merge(sequence(l, q), sequence(r, q))
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
      case _                     => node
    }
  }

  /** Normalizing ordered choice: flattens nested choices, drops failures, and prunes unreachable alternatives after a
    * total parser.
    */
  private def choice[A, B](alternatives: List[Node[A, B]]): Node[A, B] = {
    val flat = alternatives.flatMap {
      case Choice(nested) => nested
      case Failure()      => Nil
      case other          => List(other)
    }
    val (before, fromTotal) = flat.span {
      case Success() | Pure(_) => false
      case _                   => true
    }
    (before ::: fromTotal.take(1)) match {
      case Nil           => Failure()
      case single :: Nil => single
      case many          => Choice(many)
    }
  }

  override def nil[B]: Fn[Unit, Vector[B]] = {
    Fn.lift(_ => Vector.empty)
  }

  override def snoc[B]: Fn[(Vector[B], B), Vector[B]] = {
    Fn.lift((bs, b) => bs :+ b)
  }

  override def rule[A, B](self: P[A, B], label: String): P[A, B] = {
    Rule(label, self)
  }

  override def literal(expected: String): P[Unit, String] = {
    Literal(expected)
  }

  override def regex(expected: Regex): P[Unit, String] = {
    Scanner.compile(expected).fold(Pattern(expected))(Scan(expected, _))
  }

  override def not[A, B](self: P[A, B]): P[A, A] = {
    discard(self) match {
      case Failure() => Success()
      case discarded => Not(discarded)
    }
  }

  override def repeated[A, B](self: P[A, B]): P[A, Vector[B]] = {
    Repeat(self, 0, Int.MaxValue, scala.None)
  }

  override def times[A, B](self: P[A, B], n: Int): P[A, Vector[B]] = {
    require(n >= 0, "n must be non-negative")
    Repeat(self, n, n, scala.None)
  }

  override def atLeast[A, B](self: P[A, B], n: Int): P[A, Vector[B]] = {
    require(n >= 0, "n must be non-negative")
    Repeat(self, n, Int.MaxValue, scala.None)
  }

  override def separatedBy[A, B, C](self: P[A, B], separator: P[A, C]): P[A, Vector[B]] = {
    Repeat(self, 1, Int.MaxValue, Some(discard(separator)))
  }
}
