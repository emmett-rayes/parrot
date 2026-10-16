package parrot
package parser

import scala.annotation.tailrec
import scala.util.Try
import scala.util.control.NoStackTrace
import scala.util.matching.Regex

/** A matcher for regular expressions that are concatenations of single-character atoms (literal characters, escapes,
  * `.`, and character classes), each optionally quantified with `?`, `*`, or `+`.
  *
  * Atoms are matched greedily without backtracking. This agrees with [[Regex]] semantics because [[Scanner.compile]]
  * only accepts expressions where every quantified atom is disjoint from all subsequent atoms, so no character it
  * consumes could ever be matched by a later atom.
  */
final class Scanner private (atoms: Array[Scanner.Atom]) {

  /** Returns the end offset of the match anchored at `offset` in `source`, or `-1` if it does not match. */
  def scan(source: String, offset: Int): Int = {
    val length = source.length

    @tailrec
    def advance(set: CharSet, pos: Int, limit: Int): Int = {
      if pos < limit && set.contains(source.charAt(pos)) then advance(set, pos + 1, limit)
      else pos
    }

    @tailrec
    def loop(i: Int, pos: Int): Int = {
      if i >= atoms.length then pos
      else {
        val atom  = atoms(i)
        val limit = if atom.max == 1 then math.min(length, pos + 1) else length
        val end   = advance(atom.set, pos, limit)
        if end - pos < atom.min then -1
        else loop(i + 1, end)
      }
    }

    loop(0, offset)
  }

  /** The characters that can start a non-empty match, and whether the empty string matches. */
  val first: (set: CharSet, nullable: Boolean) = {
    val (optional, required) = atoms.span(_.min == 0)
    val init                 = optional ++ required.take(1)
    (set = init.foldLeft(CharSet.empty)((acc, atom) => acc.union(atom.set)), nullable = required.isEmpty)
  }
}

object Scanner {

  /** A single-character pattern `set` repeated between `min` and `max` times. */
  final private case class Atom(set: CharSet, min: Int, max: Int)

  /** Compiles `regex` into a [[Scanner]] if it belongs to the supported fragment. */
  def compile(regex: Regex): Option[Scanner] = {
    Try(Compiler(regex.regex).result()).toOption
  }

  /** Signalled when a regular expression uses constructs outside the supported fragment. */
  private object Unsupported extends Exception with NoStackTrace

  private val lineTerminators = CharSet.of('\n', '\r', '\u0085', '\u2028', '\u2029')
  private val digit           = CharSet.range('0', '9')
  private val hexDigit        = digit.union(CharSet.range('a', 'f')).union(CharSet.range('A', 'F'))
  private val word            =
    CharSet.range('a', 'z').union(CharSet.range('A', 'Z')).union(digit).union(CharSet.of('_'))
  private val space = CharSet.of(' ', '\t', '\n', '\u000b', '\f', '\r')

  /** Parses a regular expression string into a [[Scanner]]. */
  final private class Compiler(source: String) {
    private var pos    = 0
    private var dotAll = false

    private def peek: Option[Char] = {
      Option.when(pos < source.length)(source.charAt(pos))
    }

    private def next(): Char = {
      if pos >= source.length then throw Unsupported
      val c = source.charAt(pos)
      pos += 1
      c
    }

    /** The character set denoted by `\c` when `c` is a predefined character class escape. */
    private def classEscape(c: Char): Option[CharSet] = c match {
      case 'd' => Some(digit)
      case 'D' => Some(digit.complement)
      case 'w' => Some(word)
      case 'W' => Some(word.complement)
      case 's' => Some(space)
      case 'S' => Some(space.complement)
      case _   => None
    }

    /** The single character denoted by `\c`. */
    private def charEscape(c: Char): Char = c match {
      case 't' => '\t'
      case 'n' => '\n'
      case 'r' => '\r'
      case 'f' => '\f'
      case 'u' =>
        val hex = source.slice(pos, pos + 4)
        if hex.length != 4 || !hex.forall(hexDigit.contains) then throw Unsupported
        pos += 4
        hex.foldLeft(0)((n, d) => (n << 4) + d.asDigit).toChar
      case c if !c.isLetterOrDigit => c
      case _                       => throw Unsupported
    }

    /** Parses an escape sequence after `\`. */
    private def escape(): CharSet = {
      val c = next()
      classEscape(c).getOrElse(CharSet.of(charEscape(c)))
    }

    /** Parses a single character inside `[...]`, for use as a literal or range bound. */
    private def classChar(): Char = next() match {
      case '\\'      => charEscape(next())
      case '[' | '&' => throw Unsupported
      case c         => c
    }

    /** Parses a bracketed character class `[...]` after the opening `[`. */
    private def charClass(): CharSet = {
      val negated = peek.contains('^')
      if negated then pos += 1
      if peek.contains(']') then throw Unsupported

      @tailrec
      def loop(set: CharSet): CharSet = {
        if peek.contains(']') then {
          pos += 1
          if negated then set.complement else set
        } else {
          val escaped =
            if peek.contains('\\') && pos + 1 < source.length then classEscape(source.charAt(pos + 1))
            else None
          escaped match {
            case Some(cls) =>
              pos += 2
              loop(set.union(cls))
            case None =>
              val lo = classChar()
              if peek.contains('-') && pos + 1 < source.length && source.charAt(pos + 1) != ']' then {
                pos += 1
                val hi = classChar()
                if hi < lo then throw Unsupported
                loop(set.union(CharSet.range(lo, hi)))
              } else loop(set.union(CharSet.of(lo)))
          }
        }
      }

      loop(CharSet.empty)
    }

    /** Parses a single unquantified atom. */
    private def atom(): CharSet = next() match {
      case '['  => charClass()
      case '\\' => escape()
      case '.'  => if dotAll then CharSet.all else lineTerminators.complement
      case '^' | '$' | '|' | '?' | '*' | '+' | '(' | ')' | ']' | '{' | '}' => throw Unsupported
      case c                                                               => CharSet.of(c)
    }

    /** Compiles `source` into a [[Scanner]], or throws [[Unsupported]]. */
    def result(): Scanner = {
      if source.startsWith("(?s)") then {
        dotAll = true
        pos = 4
      }

      @tailrec
      def parseAtoms(acc: Vector[Atom]): Vector[Atom] = {
        if pos >= source.length then acc
        else {
          val set        = atom()
          val (min, max) = peek match {
            case Some('?') => pos += 1; (0, 1)
            case Some('*') => pos += 1; (0, Int.MaxValue)
            case Some('+') => pos += 1; (1, Int.MaxValue)
            case _         => (1, 1)
          }
          if peek.exists(c => c == '?' || c == '+' || c == '{') then throw Unsupported
          parseAtoms(acc :+ Atom(set, min, max))
        }
      }

      val atoms = parseAtoms(Vector.empty)
      val valid = atoms.tails.forall {
        case a +: rest if a.min != a.max => !rest.exists(_.set.intersects(a.set))
        case _                           => true
      }
      if !valid then throw Unsupported
      new Scanner(atoms.toArray)
    }
  }
}
