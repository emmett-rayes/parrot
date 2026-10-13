package parrot
package parser

import category.*
import category.Profunctor.on

/** Implements sequential composition and embedding from a promonad structure on `Self` over `On`. */
trait Sequencing extends ParserAlgebra {
  override type Self[_, _]: Promonad on On

  val SelfIsPromonad: Self is Promonad on On = summon
  import SelfIsPromonad.*

  override def pure[A, B](f: A ==> B): P[A, B] = {
    unit(f)
  }

  override def success[A]: P[A, A] = {
    identity[A]
  }

  override def andThen[A, B, C](self: P[A, B], other: P[B, C]): P[A, C] = {
    self >>> other
  }

  override def map[A, B, D](self: P[A, B], g: B ==> D): P[A, D] = {
    self.rmap(g)
  }

  override def mapInput[A, B, C](self: P[A, B], f: C ==> A): P[C, B] = {
    self.lmap(f)
  }
}
