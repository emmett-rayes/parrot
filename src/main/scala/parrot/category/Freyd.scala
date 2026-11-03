package parrot
package category

import scala.annotation.targetName

/** A Freyd category **K** on a promonad *P* over **C**.
  *
  * Represents the category of arrows of *P* with a bistrong structure (**C**, ⊗, *τ*, *τ*′), where
  *   - **C** is a symmetric monoidal base category
  *   - the right strength *τ*′ is the right whiskering
  *   - the left strength *τ* is the left whiskering
  *   - *p* ⋉ *q* = *τ*(*q*) ∘ *τ*′(*p*) runs *p*, then *q*
  *   - *p* ⋊ *q* = *τ*′(*p*) ∘ *τ*(*q*) runs *q*, then *p*
  *
  * **K** is a symmetric premonoidal category. Pure morphisms in **C** interchange with arrows in **K**.
  */
final class Freyd(tracked override val promonad: Promonad, tracked val strong: Bistrong.On[promonad.type])
    extends Promonad.Arrows(promonad) {
  import strong.monoidal.{`*`, ***}
  import promonad.category.--> as ==>

  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = strong.monoidal.tensor.objects[A, B]

  /** The right whiskering *τ*′: *P*(*A*,*B*) → *P*(*A* ⊗ *C*,*B* ⊗ *C*). */
  final def first[A: Obj, B: Obj, C: Obj](p: A --> B): (A * C) --> (B * C) = {
    strong.right[A, B, C](p)
  }

  /** The left whiskering *τ*: *P*(*A*,*B*) → *P*(*C* ⊗ *A*,*C* ⊗ *B*). */
  final def second[A: Obj, B: Obj, C: Obj](p: A --> B): (C * A) --> (C * B) = {
    strong.left[A, B, C](p)
  }

  /** Runs *p*, then *q*, side by side: *p* ⋉ *q*. */
  final def leftToRight[A: Obj, B: Obj, C: Obj, D: Obj](p: A --> B, q: C --> D): (A * C) --> (B * D) = {
    first[A, B, C](p) >>> second[C, D, B](q)
  }

  /** Runs *q*, then *p*, side by side: *p* ⋊ *q*. */
  final def rightToLeft[A: Obj, B: Obj, C: Obj, D: Obj](p: A --> B, q: C --> D): (A * C) --> (B * D) = {
    second[C, D, A](q) >>> first[A, B, D](p)
  }

  extension [A: Obj, B: Obj](p: A --> B)
    /** Infix extension for [[leftToRight]]. */
    @targetName("leftToRightExt")
    final def *>*[C: Obj, D: Obj](q: C --> D): (A * C) --> (B * D) = {
      leftToRight(p, q)
    }

  extension [A: Obj, B: Obj](p: A --> B)
    /** Infix extension for [[rightToLeft]]. */
    @targetName("rightToLeftExt")
    final def *<*[C: Obj, D: Obj](q: C --> D): (A * C) --> (B * D) = {
      rightToLeft(p, q)
    }

  /** Laws that every `Freyd` must satisfy. */
  object FreydLaws {

    /** *τ*′(*unit*(*f*)) = *unit*(*f* ⊗ *id*)
      */
    def unit[A: Obj, B: Obj, C: Obj](f: A ==> B)(using ((A * C) --> (B * C)) is Observable): Boolean = {
      first[A, B, C](promonad.unit(f)) =?= promonad.unit(f *** promonad.category.identity[C])
    }

    /** *τ*′(*q* ∘ *p*) = *τ*′(*q*) ∘ *τ*′(*p*)
      */
    def multiply[A: Obj, B1: Obj, B2: Obj, C: Obj](p: A --> B1, q: B1 --> B2)(
      using ((A * C) --> (B2 * C)) is Observable
    ): Boolean = {
      first[A, B2, C](p >>> q) =?= (first[A, B1, C](p) >>> first[B1, B2, C](q))
    }
  }
}

object Freyd {

  /** The Freyd categories on a promonad *P*. */
  type On[P <: Promonad] = Freyd { val promonad: P }
}
