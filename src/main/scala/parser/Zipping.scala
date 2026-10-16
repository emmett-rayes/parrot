package parrot
package parser

import category.*

/** Implements parallel composition from a strength of `Self` over `On`. */
trait Zipping extends ParserAlgebra {
  override type Self[_, _]: Strong.on[On, Empty, Pair] as ZippingStrong

  val SelfIsStrong: Self is Strong.on[On, Empty, Pair] = ZippingStrong
  import SelfIsStrong.{first, second}

  override def zip[A, B, C, D](self: P[A, B], other: P[C, D]): P[A * C, B * D] = {
    self.first >> other.second
  }
}
