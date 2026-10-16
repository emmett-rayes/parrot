package parrot
package parser

import category.Enriched.over
import category.{Enriched, Monoid}

/** Implements failure and ordered choice from an additive monoid enrichment on `Self`. */
trait Alternation extends ParserAlgebra {
  override type Self[_, _]: Enriched over Monoid.Additive as AlternationEnriched

  val SelfIsAdditive: Self is Enriched over Monoid.Additive = AlternationEnriched
  import SelfIsAdditive.HomIsV

  override def failure[A, B]: P[A, B] = {
    HomIsV.zero
  }

  override def orElse[A, B](self: P[A, B], other: P[A, B]): P[A, B] = {
    self + other
  }
}
