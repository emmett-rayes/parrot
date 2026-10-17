package parrot
package parser

import category.{Cartesian, Cocartesian}

/** Implements concatenation combinators from cartesian and cocartesian structure on `On`. */
trait Concatenation extends ParserAlgebra {
  override type On[_, _]: {Cartesian.`with`[Empty, Pair] as ConcatenationOnCartesian,
    Cocartesian.`with`[None, Alternative] as ConcatenationOnCocartesian}

  val OnIsCartesian: On is Cartesian.`with`[Empty, Pair]           = ConcatenationOnCartesian
  val OnIsCocartesian: On is Cocartesian.`with`[None, Alternative] = ConcatenationOnCocartesian

  import OnIsCartesian.*
  import OnIsCartesian.SelfIsPromonad.{>>>, identity, ~>}
  import OnIsCocartesian.{left, right}

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

  /** The empty collection. */
  def nil[B]: Empty --> Many[B]

  /** Appends a result to a collection. */
  def snoc[B]: (Many[B] * B) --> Many[B]

  /** Pairs the semantic input with the empty collection. */
  private def start[A, B]: P[A, A * Many[B]] = {
    pure(identity[A] &&& (augment >>> nil))
  }

  /** Runs `item` once, appending its result: (*a*, *bs*) ↦ (*a*, *bs* :+ *item*(*a*)). */
  private def step[A, B](item: P[A, B]): P[A * Many[B], A * Many[B]] = {
    val reshape: (A * Many[B]) ~> (A * (Many[B] * A)) = first &&& (second &&& first)
    val finish: (A * (Many[B] * B)) ~> (A * Many[B])  = identity *** snoc
    (success[A] ** (success[Many[B]] ** item)).mapInput(reshape).map(finish)
  }

  /** Runs `seed`, then `item` until it fails. */
  private def repeat[A, B](seed: P[A, A * Many[B]], item: P[A, B]): P[A, Many[B]] = {
    val next: P[A * Many[B], Many[B] + (A * Many[B])] = step(item).map(right)
    val done: P[A * Many[B], Many[B] + (A * Many[B])] = pure(second >>> left)
    seed >> (next |> done).iterate
  }

  /** Runs `item` exactly `n` times. */
  private def unrolled[A, B](item: P[A, B], n: Int): P[A, A * Many[B]] = {
    require(n >= 0, "n must be non-negative")
    (0 until n).foldLeft(start)((acc, _) => acc >> step(item))
  }

  override def repeated[A, B](self: P[A, B]): P[A, Many[B]] = {
    repeat(start, self)
  }

  override def times[A, B](self: P[A, B], n: Int): P[A, Many[B]] = {
    unrolled(self, n).map(second)
  }

  override def atLeast[A, B](self: P[A, B], n: Int): P[A, Many[B]] = {
    repeat(unrolled(self, n), self)
  }

  override def separatedBy[A, B, C](self: P[A, B], separator: P[A, C]): P[A, Many[B]] = {
    repeat(unrolled(self, 1), separator *> self)
  }
}
