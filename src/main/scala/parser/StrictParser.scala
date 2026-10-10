package parrot
package parser

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
  *   - `p.zip(success)` becomes `First(p)`
  *
  * Combinators whose derivation cannot be fused this way (`not`, repetition) are implemented with dedicated nodes. At
  * run time, a single mutable [[State]] carries the position, and failure is signalled by the [[Failed]] sentinel
  * instead of a result wrapper.
  *
  * ==Strictness of the unit==
  *
  * The unit is strict *on terms*, not *on types*: `Pair` stays `Tuple2` and `Empty` stays `Unit`, while the unitors and
  * projections that witness *I* ⊗ *A* ≅ *A* are eliminated by normalization before any tuple is built. Making it strict
  * on types with a match type (`Pair[Unit, B] = B`, `Pair[A, Unit] = A`, otherwise `(A, B)`) is unsound for the
  * generic mixins: the projection *π*₂: *A* ⊗ *B* ==> *B* is not determined by its (reduced) type. Its runtime value
  * must be `identity` at `Pair[Unit, (X, Y)]` but `_._2` at `Pair[X, Y]`, which both reduce to `(X, Y)` and share
  * a representation. Parametric code such as `Pairing` constructs *π*₂ with *A* and *B* abstract (where the match type
  * is stuck), so it cannot choose. A type-strict variant would need shape-indexed morphisms (`Shape[A]` evidence on
  * every projection and on [[zip]]), which the assumption-free root signatures deliberately do not carry. By Mac Lane's
  * coherence theorem, normalizing the structural morphisms is equivalent and stays parametric.
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

  /** The failure sentinel. */
  object Failed

  /** The result of running a node: a value of `B` or [[Failed]]. */
  type Out[B] = B | Failed.type

  private inline def failed(out: Any): Boolean = out.asInstanceOf[AnyRef] eq Failed

  /** The mutable state of a single run: the current position and the furthest failure. */
  final class State(val source: String) {
    var offset: Int      = 0
    var failedAt: Int    = -1
    var expected: String = ""

    def fail(label: String): Failed.type = {
      if offset > failedAt then {
        failedAt = offset
        expected = label
      }
      Failed
    }
  }

  extension [B](self: P[Unit, B])
    /** Runs `self` on a prefix of `source`. */
    def parse(source: String): Either[(offset: Int, expected: String), (value: B, offset: Int)] = {
      val state = State(source)
      val out   = self.run((), state)
      if failed(out) then Left((offset = state.failedAt, expected = state.expected))
      else Right((value = out.asInstanceOf[B], offset = state.offset))
    }

    /** Runs `self` on the whole of `source`. */
    def parseAll(source: String): Either[(offset: Int, expected: String), (value: B, offset: Int)] = {
      self.thenSkip(regex("(?s).".r).not).parse(source)
    }

  // ===========================================================================
  // Reified parsers
  // ===========================================================================

  /** A reified parser. */
  sealed abstract class Node[A, B] {
    def run(a: A, s: State): Out[B]
  }

  object Node {
    final case class Rule[A, B](label: String, p: Node[A, B]) extends Node[A, B] {
      def run(a: A, s: State): Out[B] = {
        val start = s.offset
        val out   = p.run(a, s)
        if failed(out) && s.failedAt == start then s.expected = label
        out
      }
    }

    final case class Literal(expected: String) extends Node[Unit, String] {
      def run(a: Unit, s: State): Out[String] = {
        if s.source.startsWith(expected, s.offset) then {
          s.offset += expected.length
          expected
        } else s.fail(s"\"$expected\"")
      }
    }

    final case class Pattern(expected: Regex) extends Node[Unit, String] {
      def run(a: Unit, s: State): Out[String] = {
        val matcher = expected.pattern.matcher(s.source).region(s.offset, s.source.length)
        if matcher.lookingAt() then {
          s.offset = matcher.end()
          matcher.group()
        } else s.fail(s"/${expected.regex}/")
      }
    }

    final case class Pure[A, B](f: Fn[A, B]) extends Node[A, B] {
      def run(a: A, s: State): Out[B] = f(a)
    }

    final case class Success[A]() extends Node[A, A] {
      def run(a: A, s: State): Out[A] = a
    }

    final case class Failure[A, B]() extends Node[A, B] {
      def run(a: A, s: State): Out[B] = s.fail("failure")
    }

    final case class Seq[A, B, C](p: Node[A, B], q: Node[B, C]) extends Node[A, C] {
      def run(a: A, s: State): Out[C] = {
        val b = p.run(a, s)
        if failed(b) then Failed else q.run(b.asInstanceOf[B], s)
      }
    }

    final case class Zip[A, B, C, D](p: Node[A, B], q: Node[C, D]) extends Node[(A, C), (B, D)] {
      def run(ac: (A, C), s: State): Out[(B, D)] = {
        val b = p.run(ac._1, s)
        if failed(b) then Failed
        else {
          val d = q.run(ac._2, s)
          if failed(d) then Failed else (b.asInstanceOf[B], d.asInstanceOf[D])
        }
      }
    }

    final case class First[A, B, C](p: Node[A, B]) extends Node[(A, C), (B, C)] {
      def run(ac: (A, C), s: State): Out[(B, C)] = {
        val b = p.run(ac._1, s)
        if failed(b) then Failed else (b.asInstanceOf[B], ac._2)
      }
    }

    final case class Pair[A, B, C](p: Node[A, B], q: Node[A, C]) extends Node[A, (B, C)] {
      def run(a: A, s: State): Out[(B, C)] = {
        val b = p.run(a, s)
        if failed(b) then Failed
        else {
          val c = q.run(a, s)
          if failed(c) then Failed else (b.asInstanceOf[B], c.asInstanceOf[C])
        }
      }
    }

    final case class SkipThen[A, B, C](p: Node[A, B], q: Node[A, C]) extends Node[A, C] {
      def run(a: A, s: State): Out[C] = {
        if failed(p.run(a, s)) then Failed else q.run(a, s)
      }
    }

    final case class ThenSkip[A, B, C](p: Node[A, B], q: Node[A, C]) extends Node[A, B] {
      def run(a: A, s: State): Out[B] = {
        val b = p.run(a, s)
        if failed(b) || failed(q.run(a, s)) then Failed else b
      }
    }

    final case class Branch[A, B, C, D](p: Node[A, B], q: Node[C, D]) extends Node[Either[A, C], Either[B, D]] {
      def run(ac: Either[A, C], s: State): Out[Either[B, D]] = ac match {
        case Left(a) =>
          val b = p.run(a, s)
          if failed(b) then Failed else Left(b.asInstanceOf[B])
        case Right(c) =>
          val d = q.run(c, s)
          if failed(d) then Failed else Right(d.asInstanceOf[D])
      }
    }

    final case class Merge[A, B, C](p: Node[A, C], q: Node[B, C]) extends Node[Either[A, B], C] {
      def run(ab: Either[A, B], s: State): Out[C] = ab match {
        case Left(a)  => p.run(a, s)
        case Right(b) => q.run(b, s)
      }
    }

    final case class Alt[A, B](p: Node[A, B], q: Node[A, B]) extends Node[A, B] {
      def run(a: A, s: State): Out[B] = {
        val start = s.offset
        val b     = p.run(a, s)
        if !failed(b) then b
        else {
          s.offset = start
          q.run(a, s)
        }
      }
    }

    final case class Lookahead[A, B](p: Node[A, B]) extends Node[A, A] {
      def run(a: A, s: State): Out[A] = {
        val start = s.offset
        if failed(p.run(a, s)) then Failed
        else {
          s.offset = start
          a
        }
      }
    }

    final case class Not[A, B](p: Node[A, B]) extends Node[A, A] {
      def run(a: A, s: State): Out[A] = {
        val start = s.offset
        val out   = p.run(a, s)
        s.offset = start
        if failed(out) then a else s.fail("not")
      }
    }

    final case class Loop[A, B](p: Node[A, Either[B, A]]) extends Node[A, B] {
      def run(a: A, s: State): Out[B] = {
        @annotation.tailrec
        def go(a: A): Out[B] = {
          val out = p.run(a, s)
          if failed(out) then Failed
          else
            out.asInstanceOf[Either[B, A]] match {
              case Left(b)     => b
              case Right(next) => go(next)
            }
        }
        go(a)
      }
    }

    /** Runs `p` between `min` and `max` times, separated by `separator`.
      *
      * Stops early when an iteration consumes no input, where the reference interpreter diverges.
      */
    final case class Repeat[A, B](p: Node[A, B], min: Int, max: Int, separator: Option[Node[A, ?]])
        extends Node[A, Vector[B]] {
      def run(a: A, s: State): Out[Vector[B]] = {
        val results = Vector.newBuilder[B]
        var count   = 0
        var done    = false
        while !done && count < max do {
          val start = s.offset
          val ok    = (count == 0 || separator.forall(sep => !failed(sep.run(a, s)))) && {
            val b = p.run(a, s)
            !failed(b) && { results += b.asInstanceOf[B]; true }
          }
          if !ok then {
            s.offset = start
            done = true
          } else {
            count += 1
            if s.offset == start && count >= min then done = true
          }
        }
        if count < min then Failed else results.result()
      }
    }

    /** A knot for [[recursive]]; `body` is tied after construction. */
    final class Rec[A, B] extends Node[A, B] {
      var body: Node[A, B] | Null = null

      def run(a: A, s: State): Out[B] = body.nn.run(a, s)

      override def toString: String = "Rec"
    }
  }

  import Node.*

  private type N = Node[Any, Any]

  private def any(n: Node[?, ?]): N = n.asInstanceOf[N]

  private def anyFn(f: Fn[?, ?]): Fn[Any, Any] = f.asInstanceOf[Fn[Any, Any]]

  /** Normalizing sequential composition. Right-associates so that redexes surface at the head. */
  private def sequence(p: N, q: N): N = {
    ((p, q): (Node[?, ?], Node[?, ?])) match {
      case (Success(), _)                                => q
      case (_, Success())                                => p
      case (Failure(), _)                                => any(Failure())
      case (Pure(f), Pure(g))                            => any(pure(Fn.andThen(anyFn(f), anyFn(g))))
      case (Pure(Fn.Fanout(Fn.Id(), Fn.Id())), Zip(l, r)) => any(Pair(any(l), any(r)))
      case (Pair(l, r), Pure(Fn.Proj1()))                => any(ThenSkip(any(l), any(r)))
      case (Pair(l, r), Pure(Fn.Proj2()))                => any(SkipThen(any(l), any(r)))
      case (Branch(l, r), Pure(Fn.Copair(f, g)))         =>
        any(Merge(sequence(any(l), any(pure(anyFn(f)))), sequence(any(r), any(pure(anyFn(g))))))
      case (Seq(l, r), _)                                => sequence(any(l), sequence(any(r), q))
      case (_, Seq(l, r))                                =>
        sequence(p, any(l)) match {
          case Seq(x, y) if (x eq p) && (y eq l) => any(Seq(p, q))
          case fused                             => sequence(fused, any(r))
        }
      case _ => any(Seq(p, q))
    }
  }

  // ===========================================================================
  // Primitives (smart constructors)
  // ===========================================================================

  extension [A, B](self: P[A, B])
    override def rule(label: String): P[A, B] = Rule(label, self)

  override def literal(expected: String): P[Unit, String] = Literal(expected)

  override def regex(expected: Regex): P[Unit, String] = Pattern(expected)

  override def pure[A, B](f: Fn[A, B]): P[A, B] = {
    (f: Fn[?, ?]) match {
      case Fn.Id() => Success().asInstanceOf[P[A, B]]
      case _       => Pure(f)
    }
  }

  override def success[A]: P[A, A] = Success()

  override def failure[A, B]: P[A, B] = Failure()

  extension [A, B](self: P[A, B])
    override def andThen[C](other: P[B, C]): P[A, C] = sequence(any(self), any(other)).asInstanceOf[P[A, C]]

    override def zip[C, D](other: P[C, D]): P[(A, C), (B, D)] = {
      (other: Node[?, ?]) match {
        case Success() => First(self).asInstanceOf[P[(A, C), (B, D)]]
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

    override def orElse(other: P[A, B]): P[A, B] = {
      ((self, other): (Node[?, ?], Node[?, ?])) match {
        case (Failure(), _)          => other
        case (_, Failure())          => self
        case (Success() | Pure(_), _) => self
        case _                       => Alt(self, other)
      }
    }

    override def lookahead: P[A, A] = {
      (self: Node[?, ?]) match {
        case Success() | Pure(_) => Success()
        case Lookahead(_)        => self.asInstanceOf[P[A, A]]
        case _                   => Lookahead(self)
      }
    }

    override def not: P[A, A] = {
      (self: Node[?, ?]) match {
        case Failure() => Success()
        case _         => Not(self)
      }
    }

    override def repeated: P[A, Vector[B]] = Repeat(self, 0, Int.MaxValue, None)

    override def times(n: Int): P[A, Vector[B]] = {
      require(n >= 0, "n must be non-negative")
      Repeat(self, n, n, None)
    }

    override def atLeast(n: Int): P[A, Vector[B]] = {
      require(n >= 0, "n must be non-negative")
      Repeat(self, n, Int.MaxValue, None)
    }

    override def separatedBy[C](separator: P[A, C]): P[A, Vector[B]] = Repeat(self, 1, Int.MaxValue, Some(separator))

  extension [A, B](self: P[A, Either[B, A]])
    override def loop: P[A, B] = Loop(self)

  override def recursive[A, B](f: P[A, B] => P[A, B]): P[A, B] = {
    val knot = Rec[A, B]()
    knot.body = f(knot)
    knot
  }
}
