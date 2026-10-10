package parrot
package parser

import scala.compiletime.asMatchable
import scala.util.matching.Regex

/** An immutable set of UTF-16 code units, stored as sorted, disjoint, non-adjacent inclusive ranges, with a bitmask for
  * ASCII membership tests.
  */
final class CharSet private (private val ranges: Array[Int]) {
  private val ascii0: Long = mask(0)
  private val ascii1: Long = mask(64)

  private def mask(from: Int): Long = {
    var bits = 0L
    var i    = 0
    while i < ranges.length do {
      val lo = math.max(ranges(i), from)
      val hi = math.min(ranges(i + 1), from + 63)
      var c  = lo
      while c <= hi do {
        bits |= 1L << (c - from)
        c += 1
      }
      i += 2
    }
    bits
  }

  def contains(c: Char): Boolean = {
    if c < 64 then (ascii0 >>> c & 1L) != 0
    else if c < 128 then (ascii1 >>> (c - 64) & 1L) != 0
    else {
      var lo = 0
      var hi = ranges.length / 2 - 1
      while lo <= hi do {
        val mid = (lo + hi) >>> 1
        if c < ranges(2 * mid) then hi = mid - 1
        else if c > ranges(2 * mid + 1) then lo = mid + 1
        else return true
      }
      false
    }
  }

  def isEmpty: Boolean = ranges.isEmpty

  /** True if some member is not ASCII. */
  def hasNonAscii: Boolean = ranges.nonEmpty && ranges(ranges.length - 1) >= 128

  def union(that: CharSet): CharSet = CharSet.normalize(this.ranges ++ that.ranges)

  def complement: CharSet = {
    val out  = Array.newBuilder[Int]
    var next = 0
    var i    = 0
    while i < ranges.length do {
      if ranges(i) > next then out ++= Array(next, ranges(i) - 1)
      next = ranges(i + 1) + 1
      i += 2
    }
    if next <= Char.MaxValue then out ++= Array(next, Char.MaxValue.toInt)
    new CharSet(out.result())
  }

  def intersects(that: CharSet): Boolean = {
    var i = 0
    var j = 0
    while i < ranges.length && j < that.ranges.length do {
      if ranges(i + 1) < that.ranges(j) then i += 2
      else if that.ranges(j + 1) < ranges(i) then j += 2
      else return true
    }
    false
  }

  override def equals(other: Any): Boolean = other.asMatchable match {
    case that: CharSet => java.util.Arrays.equals(ranges, that.ranges)
    case _             => false
  }

  override def hashCode: Int = java.util.Arrays.hashCode(ranges)

  override def toString: String = {
    ranges.grouped(2).map(r => if r(0) == r(1) then f"\\u${r(0)}%04x" else f"\\u${r(0)}%04x-\\u${r(1)}%04x")
      .mkString("[", "", "]")
  }
}

object CharSet {
  given CanEqual[CharSet, CharSet] = CanEqual.derived

  val empty: CharSet = new CharSet(Array.emptyIntArray)

  val all: CharSet = range(0, Char.MaxValue)

  def of(c: Char): CharSet = range(c, c)

  def range(from: Int, to: Int): CharSet = normalize(Array(from, to))

  /** Sorts and merges overlapping or adjacent ranges. */
  private def normalize(ranges: Array[Int]): CharSet = {
    val sorted = ranges.grouped(2).filter(r => r(0) <= r(1)).toArray.sortBy(_(0))
    val out    = Array.newBuilder[Int]
    var i      = 0
    while i < sorted.length do {
      val lo = sorted(i)(0)
      var hi = sorted(i)(1)
      i += 1
      while i < sorted.length && sorted(i)(0) <= hi + 1 do {
        hi = math.max(hi, sorted(i)(1))
        i += 1
      }
      out ++= Array(lo, hi)
    }
    new CharSet(out.result())
  }
}

/** A matcher for the regular expressions that are concatenations of single-character atoms (literal characters,
  * escapes, `.` and character classes), each optionally quantified with `?`, `*` or `+`.
  *
  * Atoms are matched greedily and never give characters back. This agrees with backtracking regular expression
  * semantics because [[Scanner.compile]] only accepts expressions where every quantified atom is disjoint from all the
  * atoms after it, so no character it consumes could ever be matched by a later atom.
  */
final class Scanner private (sets: Array[CharSet], mins: Array[Int], maxs: Array[Int]) {

  /** The end of the match anchored at `offset`, or -1. */
  def scan(source: String, offset: Int): Int = {
    val length = source.length
    var pos    = offset
    var i      = 0
    while i < sets.length do {
      val set   = sets(i)
      val max   = maxs(i)
      var count = 0
      while count < max && pos < length && set.contains(source.charAt(pos)) do {
        pos += 1
        count += 1
      }
      if count < mins(i) then return -1
      i += 1
    }
    pos
  }

  /** The characters that can start a non-empty match, and whether the empty string matches. */
  def first: (set: CharSet, nullable: Boolean) = {
    var set = CharSet.empty
    var i   = 0
    while i < sets.length do {
      set = set.union(sets(i))
      if mins(i) > 0 then return (set = set, nullable = false)
      i += 1
    }
    (set = set, nullable = true)
  }
}

object Scanner {

  /** Compiles `regex` into a [[Scanner]], if it is in the supported fragment. */
  def compile(regex: Regex): Option[Scanner] = {
    val inline = if regex.regex.startsWith("(?s)") then java.util.regex.Pattern.DOTALL else 0
    if regex.pattern.flags() != inline then scala.None
    else
      try Some(Compiler(regex.regex).result())
      catch case _: Unsupported.type => scala.None
  }

  private object Unsupported extends Exception with scala.util.control.NoStackTrace

  private val lineTerminators = Seq('\n', '\r', '\u0085', '\u2028', '\u2029').map(CharSet.of).reduce(_.union(_))

  private val digit = CharSet.range('0', '9')
  private val word  = Seq(CharSet.range('a', 'z'), CharSet.range('A', 'Z'), digit, CharSet.of('_')).reduce(_.union(_))
  private val space = Seq(' ', '\t', '\n', '\u000b', '\f', '\r').map(CharSet.of).reduce(_.union(_))

  final private class Compiler(source: String) {
    private var pos    = 0
    private var dotAll = false

    private def peek: Int = if pos < source.length then source.charAt(pos) else -1

    private def next(): Char = {
      if pos >= source.length then throw Unsupported
      val c = source.charAt(pos)
      pos += 1
      c
    }

    /** The class denoted by the escape `\c`, if it is a class escape. */
    private def classEscape(c: Char): Option[CharSet] = c match {
      case 'd' => Some(digit)
      case 'D' => Some(digit.complement)
      case 'w' => Some(word)
      case 'W' => Some(word.complement)
      case 's' => Some(space)
      case 'S' => Some(space.complement)
      case _   => scala.None
    }

    /** The character denoted by the escape `\c`. */
    private def charEscape(c: Char): Char = c match {
      case 't' => '\t'
      case 'n' => '\n'
      case 'r' => '\r'
      case 'f' => '\f'
      case 'u' =>
        val hex = source.substring(pos, math.min(pos + 4, source.length)).nn
        if hex.length != 4 || !hex.forall(Character.digit(_, 16) >= 0) then throw Unsupported
        pos += 4
        Integer.parseInt(hex, 16).toChar
      case c if !c.isLetterOrDigit => c
      case _                       => throw Unsupported
    }

    private def escape(): CharSet = {
      val c = next()
      classEscape(c).getOrElse(CharSet.of(charEscape(c)))
    }

    /** A single character inside a class, for use as a range bound. */
    private def classChar(): Char = next() match {
      case '\\'      => charEscape(next())
      case '[' | '&' => throw Unsupported
      case c         => c
    }

    private def charClass(): CharSet = {
      val negated = peek == '^'
      if negated then pos += 1
      if peek == ']' then throw Unsupported
      var set = CharSet.empty
      while peek != ']' do {
        val escaped =
          if peek == '\\' && pos + 1 < source.length then classEscape(source.charAt(pos + 1)) else scala.None
        if escaped.isDefined then {
          pos += 2
          set = set.union(escaped.get)
        } else {
          val lo = classChar()
          if peek == '-' && pos + 1 < source.length && source.charAt(pos + 1) != ']' then {
            pos += 1
            val hi = classChar()
            if hi < lo then throw Unsupported
            set = set.union(CharSet.range(lo, hi))
          } else set = set.union(CharSet.of(lo))
        }
      }
      pos += 1
      if negated then set.complement else set
    }

    private def atom(): CharSet = next() match {
      case '['  => charClass()
      case '\\' => escape()
      case '.'  => if dotAll then CharSet.all else lineTerminators.complement
      case '^' | '$' | '|' | '?' | '*' | '+' | '(' | ')' | ']' | '{' | '}' => throw Unsupported
      case c                                                               => CharSet.of(c)
    }

    def result(): Scanner = {
      if source.startsWith("(?s)") then {
        dotAll = true
        pos = 4
      }
      val sets = Array.newBuilder[CharSet]
      val mins = Array.newBuilder[Int]
      val maxs = Array.newBuilder[Int]
      while pos < source.length do {
        sets += atom()
        val (min, max) = peek match {
          case '?' => pos += 1; (0, 1)
          case '*' => pos += 1; (0, Int.MaxValue)
          case '+' => pos += 1; (1, Int.MaxValue)
          case _   => (1, 1)
        }
        if peek == '?' || peek == '+' || peek == '{' then throw Unsupported
        mins += min
        maxs += max
      }
      val s = sets.result()
      val l = mins.result()
      val h = maxs.result()
      for i <- s.indices if l(i) != h(i); j <- (i + 1) until s.length do if s(i).intersects(s(j)) then throw Unsupported
      new Scanner(s, l, h)
    }
  }
}
