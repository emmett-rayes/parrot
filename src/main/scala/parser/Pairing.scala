package parrot
package parser

import category.*

/** Implements paired sequencing from a cartesian structure on `On`. */
trait Pairing extends ParserAlgebra {
  override type On[_, _]: Cartesian.`with`[Empty, Pair]

  val OnIsCartesian: On is Cartesian.`with`[Empty, Pair] = summon
  import OnIsCartesian.{diagonal, first, second}

  override def pair[A, B, C](self: P[A, B], other: P[A, C]): P[A, B * C] = {
    (self ** other).mapInput(diagonal)
  }

  override def skipThen[A, B, C](self: P[A, B], other: P[A, C]): P[A, C] = {
    (self && other).map(second)
  }

  override def thenSkip[A, B, C](self: P[A, B], other: P[A, C]): P[A, B] = {
    (self && other).map(first)
  }

  override def between[A, B, C, D](self: P[A, B], open: P[A, C], close: P[A, D]): P[A, B] = {
    open *> self <* close
  }
}
