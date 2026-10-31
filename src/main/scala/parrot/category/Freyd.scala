package parrot
package category

import scala.annotation.targetName

/** A Freyd category on a promonad *P* over **K**: its category of arrows, with a strength over ⊗ that *unit* and
  * composition preserve.
  *
  * Represents the category of arrows of *P* with a bistrong structure *S*, where
  *   - *first*(*unit*(*f*)) = *unit*(*f* ⊗ *id*): pure morphisms act as their tensor
  *   - *first*(*q* ∘ *p*) = *first*(*q*) ∘ *first*(*p*): the strength respects sequencing
  *   - *p* ⋉ *q* = *second*(*q*) ∘ *first*(*p*) runs *p*, then *q*, side by side
  *
  * ⋉ is not a bifunctor in general: running *q* first can give a different result when both have effects, so the
  * category is premonoidal, not monoidal. Pure arrows commute with every arrow ([[FreydLaws.centrality]]).
  */
final class Freyd(tracked override val P: Promonad, tracked val S: Strong.Bistrong.On[P.type])
    extends Promonad.Arrows(P) {
  import S.M.{`*`, given}
  import P.K.--> as ==>

  /** *first*: *P*(*A*,*B*) → *P*(*A* ⊗ *C*,*B* ⊗ *C*), the right strength *τ*′: the arrow runs on the first component.
    */
  final def first[A: Obj, B: Obj, C: Obj](p: A --> B): (A * C) --> (B * C) = {
    S.right[A, B, C](p)
  }

  /** *second*: *P*(*A*,*B*) → *P*(*C* ⊗ *A*,*C* ⊗ *B*), the left strength *τ*: the arrow runs on the second component.
    */
  final def second[A: Obj, B: Obj, C: Obj](p: A --> B): (C * A) --> (C * B) = {
    S.left[A, B, C](p)
  }

  /** Runs *p*, then *q*, side by side: *p* ⋉ *q* = *second*(*q*) ∘ *first*(*p*). */
  final def parallel[A: Obj, B: Obj, C: Obj, D: Obj](p: A --> B, q: C --> D): (A * C) --> (B * D) = {
    first[A, B, C](p) >>> second[C, D, B](q)
  }

  extension [A: Obj, B: Obj](p: A --> B)
    /** Infix extension for [[parallel]]. */
    @targetName("parallelExt")
    final def **[C: Obj, D: Obj](q: C --> D): (A * C) --> (B * D) = {
      parallel(p, q)
    }

  /** Laws that make a strong promonad a Freyd category. */
  object FreydLaws {

    /** *first*(*unit*(*f*)) = *unit*(*f* ⊗ *id*)
      */
    def unit[A: Obj, B: Obj, C: Obj](f: A ==> B)(using ((A * C) --> (B * C)) is Observable): Boolean = {
      first[A, B, C](P.unit(f)) =?= P.unit(S.M.tensor(f, P.K.identity[C]))
    }

    /** *first*(*q* ∘ *p*) = *first*(*q*) ∘ *first*(*p*)
      */
    def multiply[A: Obj, B1: Obj, B2: Obj, C: Obj](p: A --> B1, q: B1 --> B2)(
      using ((A * C) --> (B2 * C)) is Observable
    ): Boolean = {
      first[A, B2, C](p >>> q) =?= (first[A, B1, C](p) >>> first[B1, B2, C](q))
    }

    /** *first*(*unit*(*f*)) ⨾ *second*(*q*) = *second*(*q*) ⨾ *first*(*unit*(*f*)): pure arrows are central.
      */
    def centrality[A: Obj, B: Obj, C: Obj, D: Obj](f: A ==> B, q: C --> D)(
      using ((A * C) --> (B * D)) is Observable
    ): Boolean = {
      (first[A, B, C](P.unit(f)) >>> second[C, D, B](q)) =?= (second[C, D, A](q) >>> first[A, B, D](P.unit(f)))
    }
  }
}
