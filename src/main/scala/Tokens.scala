package parrot

/** A token is a single character of the input to be parsed. */
type Token = Char

/** A sequence of tokens representing the input to be parsed.
  *
  * Represented as a flat, immutable window `[start, end)` into a shared backing sequence.
  */
final class Tokens private (private val underlying: Array[Token], val start: Int, val end: Int)
    extends CharSequence {

  override def equals(obj: Any): Boolean = {
    if !obj.isInstanceOf[Tokens] then false
    else {
      val that = obj.asInstanceOf[Tokens]
      (underlying eq that.underlying) && start == that.start && end == that.end
    }
  }

  /** The tokens of this window concatenated into a `String`. */
  override def toString: String = String(underlying, start, length)

  /** The hash code of this window. */
  override def hashCode: Int = (System.identityHashCode(underlying) * 31 + start) * 31 + end

  /** A copy of the underlying tokens of this window. */
  def total: Array[Token] = underlying.clone()

  /** True if this window contains no tokens. */
  override def isEmpty: Boolean = length == 0

  /** True if this window contains at least one token. */
  def nonEmpty: Boolean = length > 0

  /** The number of tokens in this window. */
  override def length: Int = end - start

  /** The character at `index`, relative to the start of this window. */
  override def charAt(index: Int): Char = apply(index)

  /** A subsequence over `[start, end)`, relative to the start of this window, bounded to this window. */
  override def subSequence(start: Int, end: Int): CharSequence = slice(start, end)

  /** A window with the first `n` tokens dropped, bounded to this window. */
  def drop(n: Int): Tokens = {
    val newStart = math.min(math.max(this.start + n, this.start), this.end)
    new Tokens(underlying, newStart, this.end)
  }

  /** A window over `[from, until)`, relative to the start of this window, bounded to this window. */
  def slice(from: Int, until: Int): Tokens = {
    val newStart = math.min(math.max(start + math.max(from, 0), start), end)
    val newEnd   = math.max(newStart, math.min(start + until, end))
    new Tokens(underlying, newStart, newEnd)
  }

  /** Substring slice without intermediate [[Tokens]] allocation. */
  def substring(from: Int, until: Int): String = {
    val newStart = math.min(math.max(start + math.max(from, 0), start), end)
    val newEnd   = math.max(newStart, math.min(start + until, end))
    String(underlying, newStart, newEnd - newStart)
  }

  /** True if this window starts with the tokens of `that`. */
  def startsWith(that: Tokens): Boolean = {
    val len = that.length
    if length < len then false
    else {
      var i       = 0
      var matched = true
      while matched && i < len do {
        if charAt(i) != that.charAt(i) then matched = false
        else i += 1
      }
      matched
    }
  }

  /** The token at `index`, relative to the start of this window. */
  def apply(index: Int): Token = underlying(start + index)

  /** Computes a snippet of the surrounding input for use in error messages. */
  def context(before: Int = 10, after: Int = 10, marker: String = "\uFF3F"): String = {
    val beforeStart = math.max(start - before, 0)
    val afterEnd    = math.min(start + after, underlying.length)
    val prefix      = (if beforeStart > 0 then "..." else "") + String(underlying, beforeStart, start - beforeStart)
    val suffix      = String(underlying, start, afterEnd - start) + (if afterEnd < underlying.length then "..." else "")
    s"$prefix$marker$suffix"
  }
}

object Tokens {

  /** Tokens are ordered by the length of their underlying windows. */
  given Ordering[Tokens] = Ordering.by(_.length)

  /** Creates a window over the entirety of `underlying`. */
  def apply(underlying: Array[Token]): Tokens = new Tokens(underlying, 0, underlying.length)
}

/** Operations for working with strings as tokens. */
extension (self: String)
  /** Converts this string into its sequence of tokens. */
  def asTokens: Tokens = Tokens(self.toCharArray)
