package parrot
package parser

import category.*
import category.Enriched.over

/** Implements recursion from a fixed-point enrichment on `Self`. */
trait Recursion extends ParserAlgebra {
  override type Self[_, _]: Self is Enriched over Fixed

  val SelfIsFixed: Self is Enriched over Fixed = summon

  override def recursive[A, B](f: P[A, B] => P[A, B]): P[A, B] = ???
}
