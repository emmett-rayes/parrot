package parrot
package parser

import category.*

/** Implements lookahead from a restriction structure on `Self`. */
trait Lookahead extends ParserAlgebra {
  override type Self[_, _]: Restriction

  val SelfIsRestriction: Self is Restriction = summon
  import SelfIsRestriction.restrict

  override def lookahead[A, B](self: P[A, B]): P[A, A] = {
    self.restrict
  }
}
