package parrot
package parser

import category.*
import category.Enriched.over

/** Implements recursion from a fixed-point enrichment on `Self`. */
trait Recursion extends ParserAlgebra {
  override type Self[_, _]: Enriched over Fixed.in[Function, Unit, LazyTuple2, Function] as RecursionEnriched

  val SelfIsFixed: Self is Enriched over Fixed.in[Function, Unit, LazyTuple2, Function] = summon

  override def recursive[A, B](f: P[A, B] => P[A, B]): P[A, B] = {
    SelfIsFixed.HomIsV[A, B].fix(f)
  }
}
