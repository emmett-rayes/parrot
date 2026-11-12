package parrot
package category

import scala.annotation.targetName

/** A Freyd category **K** on a bistrong promonad *P* over **C**.
  *
  * Represents the premonoidal category **K** of arrows of *P* with a bistrong structure (**C**, ⊗, *τ*, *τ*′), where
  *   - **C** is a symmetric monoidal base category
  *   - the tensor of **K** is the tensor of **C** on objects, with the right strength *τ*′(*p*) = *p* ⦸ *C* and the
  *     left strength *τ*(*p*) = *C* ⊘ *p* as its morphism parts
  *   - the unit, the unitors, the associator and the braiding of **K** are those of **C**, as pure arrows
  *   - *p* ⋉ *q* = *τ*(*q*) ∘ *τ*′(*p*) runs *p*, then *q*
  *   - *p* ⋊ *q* = *τ*′(*p*) ∘ *τ*(*q*) runs *q*, then *p*
  *
  * **K** is a symmetric premonoidal category. Pure morphisms in **C** interchange with arrows in **K**.
  *
  * Over a cartesian **C** this is the Freyd category of Power and Robinson. Over any symmetric monoidal **C**,
  * coproducts included, it is the centred premonoidal category of Benton and Hyland, with the functor of the pure
  * arrows as its centre. That the right strength respects composition, *τ*′(*q* ∘ *p*) = *τ*′(*q*) ∘ *τ*′(*p*), is the
  * law `lmapComposition` of its tensor, a [[BinoidalFunctor]].
  */
open class Freyd(tracked val strong: StrongPromonad)
    extends Premonoidal(
      strong.profunctor.arrows,
      strong.profunctor.arrows.Object[strong.monoidal.I](using strong.monoidal.unit.evidence),
      Freyd.Tensor(strong),
    ),
      SymmetricPremonoidal {
  import category.{Iso, Obj, -->, <->, >>>}
  import strong.monoidal.***
  import strong.profunctor
  import profunctor.category.--> as ==>

  private given IIsObj: (I is Obj)                                = unit.evidence
  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = tensor.objects[A, B]

  def leftUnitor[A: Obj]: (I * A) <-> A = {
    val iso = strong.monoidal.leftUnitor[A]
    Iso(profunctor.unit(iso.to), profunctor.unit(iso.from))
  }

  override def rightUnitor[A: Obj]: (A * I) <-> A = {
    val iso = strong.monoidal.rightUnitor[A]
    Iso(profunctor.unit(iso.to), profunctor.unit(iso.from))
  }

  def associator[A: Obj, B: Obj, C: Obj]: ((A * B) * C) <-> (A * (B * C)) = {
    val iso = strong.monoidal.associator[A, B, C]
    Iso(profunctor.unit(iso.to), profunctor.unit(iso.from))
  }

  def braid[A: Obj, B: Obj]: (A * B) --> (B * A) = {
    profunctor.unit(strong.monoidal.braid[A, B])
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
  def leftToRight[A: Obj, B: Obj, C: Obj, D: Obj](p: A --> B, q: C --> D): (A * C) --> (B * D) = {
    first[A, B, C](p) >>> second[C, D, B](q)
  }

  /** Runs *q*, then *p*, side by side: *p* ⋊ *q*. */
  def rightToLeft[A: Obj, B: Obj, C: Obj, D: Obj](p: A --> B, q: C --> D): (A * C) --> (B * D) = {
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
      first[A, B, C](profunctor.unit(f)) =?= profunctor.unit(f *** profunctor.category.identity[C])
    }

    /** *p* ⋉ *q* = *τ*(*q*) ∘ *τ*′(*p*)
      */
    def leftToRightIsStrengths[A: Obj, B: Obj, C: Obj, D: Obj](p: A --> B, q: C --> D)(
      using ((A * C) --> (B * D)) is Observable
    ): Boolean = {
      (p *>* q) =?= (first[A, B, C](p) >>> second[C, D, B](q))
    }

    /** *p* ⋊ *q* = *τ*′(*p*) ∘ *τ*(*q*)
      */
    def rightToLeftIsStrengths[A: Obj, B: Obj, C: Obj, D: Obj](p: A --> B, q: C --> D)(
      using ((A * C) --> (B * D)) is Observable
    ): Boolean = {
      (p *<* q) =?= (second[C, D, A](q) >>> first[A, B, D](p))
    }

    /** Laws that follow from the others: theorems, checked as tests. */
    object Consequences {

      /** *η*(*f*) ⋉ *q* = *η*(*f*) ⋊ *q*
        *
        * A pure arrow is central: it interchanges with every arrow *q*. It follows from [[unit]] and the dinaturality
        * of the strength.
        */
      def pureIsCentral[A: Obj, B: Obj, C: Obj, D: Obj](f: A ==> B, q: C --> D)(
        using ((A * C) --> (B * D)) is Observable
      ): Boolean = {
        (profunctor.unit(f) *>* q) =?= (profunctor.unit(f) *<* q)
      }
    }
  }
}

object Freyd {

  /** The Freyd categories on a bistrong promonad with the strength *S*. */
  type On[S <: Bistrong] = Freyd { val strong: S }

  /** The tensor of the Freyd category on a bistrong promonad *P* over **C**.
    *
    * Represents a binoidal functor on the arrows of *P*, where
    *   - *A* ⊗ *B* is the tensor of **C**
    *   - *p* ⦸ *C* = *τ*′(*p*), the right strength
    *   - *C* ⊘ *p* = *τ*(*p*), the left strength
    */
  final class Tensor(tracked val strong: StrongPromonad)
      extends BinoidalFunctor(strong.profunctor.arrows, strong.profunctor.arrows, strong.profunctor.arrows) {
    import strong.profunctor.arrows.{Obj, -->}

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
