package parrot
package parser

import scala.collection.immutable.BitSet

/** An immutable set of `Char` values, backed by a [[BitSet]] with inline bitmasks for ASCII membership tests. */
final case class CharSet private (private val bits: BitSet) {
  private val (ascii0, ascii1, nonAscii) = {
    val mask = bits.toBitMask
    val w0   = if mask.length > 0 then mask(0) else 0L
    val w1   = if mask.length > 1 then mask(1) else 0L
    (w0, w1, mask.length > 2)
  }

  /** True if `c` belongs to this set. */
  def contains(c: Char): Boolean = {
    if c < 64 then (ascii0 >>> c & 1L) != 0
    else if c < 128 then (ascii1 >>> (c - 64) & 1L) != 0
    else bits.contains(c)
  }

  /** True if this set contains no characters. */
  def isEmpty: Boolean = {
    bits.isEmpty
  }

  /** True if this set contains a non-ASCII character (`c >= 128`). */
  def hasNonAscii: Boolean = {
    nonAscii
  }

  /** The union of this set and `that`. */
  def union(that: CharSet): CharSet = {
    CharSet(bits | that.bits)
  }

  /** The complement of this set in `'\u0000'` to `'\uffff'`. */
  def complement: CharSet = {
    CharSet(CharSet.all.bits &~ bits)
  }

  /** True if this set and `that` share at least one character. */
  def intersects(that: CharSet): Boolean = {
    (bits & that.bits).nonEmpty
  }
}

object CharSet {
  given CanEqual[CharSet, CharSet] = CanEqual.derived

  /** The empty character set. */
  val empty: CharSet = CharSet(BitSet.empty)

  /** The set of all `Char` values (`'\u0000'` to `'\uffff'`). */
  val all: CharSet = CharSet(BitSet.fromBitMaskNoCopy(Array.fill(1024)(-1L)))

  /** The set containing `chars`. */
  def of(chars: Char*): CharSet = {
    CharSet(BitSet.fromSpecific(chars.map(_.toInt)))
  }

  /** The set of characters from `from` to `to` inclusive. */
  def range(from: Char, to: Char): CharSet = {
    CharSet(BitSet.fromSpecific(from.toInt to to.toInt))
  }
}
