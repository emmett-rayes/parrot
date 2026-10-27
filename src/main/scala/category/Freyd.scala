package parrot
package category

import scala.annotation.targetName

/** A Freyd category: a promonad *P* over **K** with a strength over ⊗ that *unit* and *multiply* preserve.
  *
  * Represents a strong promonad, where
  *   - *first*(*unit*(*f*)) = *unit*(*f* ⊗ *id*): pure morphisms act as their tensor
  *   - *first*(*q* ∘ *p*) = *first*(*q*) ∘ *first*(*p*): the strength respects sequencing
  *   - *p* `**` *q* = *second*(*q*) ∘ *first*(*p*) runs *p*, then *q*, side by side
  *
  * `**` is not a bifunctor in general: running *q* first can give a different result when both have effects, so the
  * arrows form a premonoidal category. Pure arrows commute with every arrow ([[FreydLaws.centrality]]). A Freyd
  * category is not a new structure but the combination of a [[Promonad]] and a [[Strong]] profunctor, so it is a bundle
  * of the two with the laws that connect them.
  */
final class Freyd(tracked val S: Strong { val P: Promonad }) {
  import S.M.{*, given}
  import S.P.P
  import S.P.K.{Obj, -->}

  extension [A: Obj, B: Obj](p: P[A, B])
    /** Runs *p*, then *q*, side by side: *second*(*q*) ∘ *first*(*p*). */
    @targetName("parallelExt")
    final def **[C: Obj, D: Obj](q: P[C, D]): P[A * C, B * D] = {
      S.P.multiply(S.second[C, D, B](q), S.first[A, B, C](p))
    }

  /** Laws that make a strong promonad a Freyd category. */
  object FreydLaws {

    /** *first*(*unit*(*f*)) = *unit*(*f* ⊗ *id*)
      */
    def unit[A: Obj, B: Obj, C: Obj](f: A --> B)(
      using P[A * C, B * C] is Observable
    ): Boolean = {
      S.first[A, B, C](S.P.unit(f)) =?= S.P.unit(S.M.tensor(f, S.P.K.identity[C]))
    }

    /** *first*(*q* ∘ *p*) = *first*(*q*) ∘ *first*(*p*)
      */
    def multiply[A: Obj, B: Obj, B2: Obj, C: Obj](p: P[A, B], q: P[B, B2])(
      using P[A * C, B2 * C] is Observable
    ): Boolean = {
      S.first[A, B2, C](S.P.multiply(q, p)) =?= S.P.multiply(S.first[B, B2, C](q), S.first[A, B, C](p))
    }

    /** *first*(*unit*(*f*)) ⨾ *second*(*q*) = *second*(*q*) ⨾ *first*(*unit*(*f*)): pure arrows are central.
      */
    def centrality[A: Obj, B: Obj, C: Obj, D: Obj](f: A --> B, q: P[C, D])(
      using P[A * C, B * D] is Observable
    ): Boolean = {
      S.P.multiply(S.second[C, D, B](q), S.first[A, B, C](S.P.unit(f))) =?=
        S.P.multiply(S.first[A, B, D](S.P.unit(f)), S.second[C, D, A](q))
    }
  }
}
