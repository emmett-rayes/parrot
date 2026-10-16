package parrot
package parser

import category.*

/** Implements iteration from an Elgot structure on `Self`. */
trait Iteration extends ParserAlgebra {
  override type Self[_, _]: Elgot.`with`[None, Alternative] as IterationElgot

  val SelfIsElgot: Self is Elgot.`with`[None, Alternative] = summon
  import SelfIsElgot.dagger

  override def iterate[A, B](self: P[A, B + A]): P[A, B] = {
    self.dagger
  }
}
