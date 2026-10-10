package parrot
package parser

import parrot.category.{Cartesian, Cocartesian, Kleisli}

/** The reference interpreter of [[ParserAlgebra]]: the specification against which other interpreters are checked.
  *
  * A [[KleisliParser]] whose pure functions are Scala functions.
  */
object ReferenceParser extends KleisliParser {

  type On[A, B] = Function[A, B]

  override val SelfIsPromonad = Kleisli.KleisliIsPromonad[Parse](using ParseIsMonad)
  override val SelfIsStrong   = Kleisli.KleisliIsStrong[Parse](using ParseIsMonad)

  override val OnIsCartesian: Cartesian.FunctionIsCartesian.type       = Cartesian.FunctionIsCartesian
  override val OnIsCocartesian: Cocartesian.FunctionIsCocartesian.type = Cocartesian.FunctionIsCocartesian

  override def nil[B]: Unit => Vector[B] = _ => Vector.empty

  override def snoc[B]: ((Vector[B], B)) => Vector[B] = (bs, b) => bs :+ b
}
