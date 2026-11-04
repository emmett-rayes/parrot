package parrot
package category

import scala.annotation.targetName

/** A Freyd category **K** on a promonad *P* over **C**.
  *
  * Represents the premonoidal category **K** of arrows of *P* with a bistrong structure (**C**, ⊗, *τ*, *τ*′), where
  *   - **C** is a symmetric monoidal base category
  *   - the tensor of **K** is the tensor of **C** on objects, with the right strength *τ*′(*p*) = *p* ⦸ *C* and the
  *     left strength *τ*(*p*) = *C* ⊘ *p* as its morphism parts
  *   - the unit, the unitors and the associator of **K** are those of **C**, as pure arrows
  *   - *p* ⋉ *q* = *τ*(*q*) ∘ *τ*′(*p*) runs *p*, then *q*
  *   - *p* ⋊ *q* = *τ*′(*p*) ∘ *τ*(*q*) runs *q*, then *p*
  *
  * **K** is a symmetric premonoidal category. Pure morphisms in **C** interchange with arrows in **K**.
  */
final class Freyd(tracked val promonad: Promonad, tracked val strong: Bistrong.On[promonad.type])
    extends Premonoidal(
      promonad.arrows,
      promonad.arrows.Object[strong.monoidal.I](using strong.monoidal.unit.evidence),
      Freyd.Tensor(promonad, strong),
    ) {
  import category.{Iso, Obj, -->, <->, >>>}
  import strong.monoidal.***
  import promonad.category.--> as ==>

  private given IIsObj: (I is Obj)                                = unit.evidence
  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = tensor.objects[A, B]

  def leftUnitor[A: Obj]: (I * A) <-> A = {
    val iso = strong.monoidal.leftUnitor[A]
    Iso(promonad.unit(iso.to), promonad.unit(iso.from))
  }

  def rightUnitor[A: Obj]: (A * I) <-> A = {
    val iso = strong.monoidal.rightUnitor[A]
    Iso(promonad.unit(iso.to), promonad.unit(iso.from))
  }

  def associator[A: Obj, B: Obj, C: Obj]: ((A * B) * C) <-> (A * (B * C)) = {
    val iso = strong.monoidal.associator[A, B, C]
    Iso(promonad.unit(iso.to), promonad.unit(iso.from))
  }

  /** The right strength *τ*′(*p*) = *p* ⦸ *C*: *P*(*A*,*B*) → *P*(*A* ⊗ *C*,*B* ⊗ *C*). */
  final def first[A: Obj, B: Obj, C: Obj](p: A --> B): (A * C) --> (B * C) = {
    lmap[A, B, C](p)
  }

  /** The left strength *τ*(*p*) = *C* ⊘ *p*: *P*(*A*,*B*) → *P*(*C* ⊗ *A*,*C* ⊗ *B*). */
  final def second[A: Obj, B: Obj, C: Obj](p: A --> B): (C * A) --> (C * B) = {
    rmap[A, B, C](p)
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

  /** The tensor of the Freyd category on a promonad *P* over **C** with a bistrong structure *S*.
    *
    * Represents a binoidal functor on the arrows of *P*, where
    *   - *A* ⊗ *B* is the tensor of **C**
    *   - *p* ⦸ *C* = *τ*′(*p*), the right strength
    *   - *C* ⊘ *p* = *τ*(*p*), the left strength
    */
  final class Tensor(tracked val promonad: Promonad, tracked val strong: Bistrong.On[promonad.type])
      extends BinoidalFunctor(promonad.arrows, promonad.arrows, promonad.arrows) {
    import promonad.arrows.{Obj, -->}

    type Self = strong.monoidal.Tensor

    def objects[A: Obj, B: Obj]: F[A, B] is Obj = {
      strong.monoidal.tensor.objects[A, B]
    }

    def lmap[A: Obj, B: Obj, C: Obj](p: A --> B): F[A, C] --> F[B, C] = {
      strong.right[A, B, C](p)
    }

    def rmap[A: Obj, B: Obj, C: Obj](p: A --> B): F[C, A] --> F[C, B] = {
      strong.left[A, B, C](p)
    }
  }
}
