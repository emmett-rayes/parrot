package parrot
package parser

import parrot.category.Profunctor.on
import parrot.category.{Kleisli, Promonad, Strong}

/** [[ReferenceParser]] with reified pure functions: a [[KleisliParser]] whose pure functions are [[Fn]].
  *
  * Parsers are the same Kleisli arrows, so this interpreter isolates the effect of [[Fn]] (normalization of the pure
  * functions built by the derived combinators, interpretation instead of closures) from the static analysis and
  * specialized nodes of [[StrictParser]].
  *
  * The Kleisli structures on **Type** restrict along the interpretation [[Fn.apply]] of `Fn` in **Type**: the unit
  * embeds a reified function by interpreting it, and everything else is unchanged.
  */
object ReferenceFnParser extends KleisliParser {

  type On[A, B] = Fn[A, B]

  private val KleisliIsPromonad = Kleisli.KleisliIsPromonad[Parse](using ParseIsMonad)
  private val KleisliIsStrong   = Kleisli.KleisliIsStrong[Parse](using ParseIsMonad)

  override val SelfIsPromonad: Kleisli[Parse] is Promonad on Fn = new Promonad {
    type Self[A, B] = A => Parse[B]
    type On         = Fn

    override val OnIsPromonad: Fn.FnIsPromonad.type = Fn.FnIsPromonad

    def unit[A, B](f: Fn[A, B]): A => Parse[B] = KleisliIsPromonad.unit(f.apply)

    def multiply[A, B, C](q: B => Parse[C], p: A => Parse[B]): A => Parse[C] = KleisliIsPromonad.multiply(q, p)
  }

  override val SelfIsStrong: Kleisli[Parse] is Strong.on[Fn, Unit, Tuple2] = new Strong {
    type Self[A, B] = A => Parse[B]

    override given given_Profunctor_Self: (Kleisli[Parse] is Promonad on Fn) = ReferenceFnParser.SelfIsPromonad
    override val SelfIsProfunctor: Kleisli[Parse] is Promonad on Fn            = given_Profunctor_Self
    override val OnIsMonoidal: Fn.FnIsCartesian.type                    = Fn.FnIsCartesian

    def first[A, B, C](p: A => Parse[B]): ((A, C)) => Parse[(B, C)] = KleisliIsStrong.first(p)

    def second[A, B, C](p: A => Parse[B]): ((C, A)) => Parse[(C, B)] = KleisliIsStrong.second(p)
  }

  override val OnIsCartesian: Fn.FnIsCartesian.type     = Fn.FnIsCartesian
  override val OnIsCocartesian: Fn.FnIsCocartesian.type = Fn.FnIsCocartesian

  override def nil[B]: Fn[Unit, Vector[B]] = Fn.lift(_ => Vector.empty)

  override def snoc[B]: Fn[(Vector[B], B), Vector[B]] = Fn.lift((bs, b) => bs :+ b)
}
