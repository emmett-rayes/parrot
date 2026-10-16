package parrot
package parser

import category.*

/** Implements lookahead from a restriction structure on `Self`. */
trait Lookahead extends ParserAlgebra {
  override type Self[_, _]: Restriction as LookaheadRestriction

  val SelfIsRestriction: Self is Restriction = LookaheadRestriction
  import SelfIsRestriction.restrict

  override def lookahead[A, B](self: P[A, B]): P[A, A] = {
    self.restrict
  }
}
