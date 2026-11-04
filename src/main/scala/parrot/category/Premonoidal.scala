package parrot
package category

/** A premonoidal structure on a category **C**.
  *
  * Represents a premonoidal category (**C**, ⊗, *I*), where
  *   - ⊗: **C** × **C** → **C** is the tensor, a binoidal functor with the whiskerings *f* ⦸ *C* and *C* ⊘ *f*
  *   - *I* is the unit object
  *   - *λ*: *I* ⊗ *A* ≅ *A* is the left unitor
  *   - *ρ*: *A* ⊗ *I* ≅ *A* is the right unitor
  *   - *α*: (*A* ⊗ *B*) ⊗ *C* ≅ *A* ⊗ (*B* ⊗ *C*) is the associator
  *
  * A morphism is central if it interchanges with every morphism, on both sides: (*B* ⊘ *g*) ∘ (*h* ⦸ *C*) =
  * (*h* ⦸ *D*) ∘ (*A* ⊘ *g*). The unitors and the associator are central, and natural in each component separately. A
  * monoidal category is a premonoidal category whose morphisms are all central.
  */
abstract class Premonoidal(
  tracked val category: Category,
  tracked val unit: category.Object,
  tracked val tensor: BinoidalFunctor.Into[category.type] { val source1: category.type; val source2: category.type },
) extends caps.Pure {
  import category.{Obj, -->, <->, >>>}

  /** The tensor *A* ⊗ *B* of objects *A* and *B*. */
  final type Tensor = tensor.F

  /** Infix alias for [[Tensor]]. */
  final type * = Tensor

  /** The unit object *I*. */
  final type I = unit.A

  private given IIsObj: (I is Obj)                                = unit.evidence
  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = tensor.objects[A, B]

  export tensor.{lmap, rmap}

  /** *λ*: *I* ⊗ *A* ≅ *A*
    */
  def leftUnitor[A: Obj]: (I * A) <-> A

  /** *ρ*: *A* ⊗ *I* ≅ *A*
    */
  def rightUnitor[A: Obj]: (A * I) <-> A

  /** *α*: (*A* ⊗ *B*) ⊗ *C* ≅ *A* ⊗ (*B* ⊗ *C*)
    */
  def associator[A: Obj, B: Obj, C: Obj]: ((A * B) * C) <-> (A * (B * C))

  /** Laws that any `Premonoidal` structure must satisfy.
    *
    * The unitors and the associator are central isomorphisms, natural in each component and coherent.
    */
  object PremonoidalLaws {
    import category.IsoLaws

    /** (*B* ⊘ *g*) ∘ (*h* ⦸ *C*) = (*h* ⦸ *D*) ∘ (*A* ⊘ *g*) */
    private def interchangesLeft[A: Obj, B: Obj, C: Obj, D: Obj](h: A --> B, g: C --> D)(
      using ((A * C) --> (B * D)) is Observable
    ): Boolean = {
      (lmap[A, B, C](h) >>> rmap[C, D, B](g)) =?= (rmap[C, D, A](g) >>> lmap[A, B, D](h))
    }

    /** (*g* ⦸ *B*) ∘ (*C* ⊘ *h*) = (*D* ⊘ *h*) ∘ (*g* ⦸ *A*) */
    private def interchangesRight[A: Obj, B: Obj, C: Obj, D: Obj](h: A --> B, g: C --> D)(
      using ((C * A) --> (D * B)) is Observable
    ): Boolean = {
      (rmap[A, B, C](h) >>> lmap[C, D, B](g)) =?= (lmap[C, D, A](g) >>> rmap[A, B, D](h))
    }

    /** *λ*⁻¹ ∘ *λ* = *id*
      */
    def leftUnitorLeftInverse[A: Obj](using ((I * A) --> (I * A)) is Observable): Boolean = {
      IsoLaws.leftInverse(leftUnitor[A])
    }

    /** *λ* ∘ *λ*⁻¹ = *id*
      */
    def leftUnitorRightInverse[A: Obj](using (A --> A) is Observable): Boolean = {
      IsoLaws.rightInverse(leftUnitor[A])
    }

    /** *ρ*⁻¹ ∘ *ρ* = *id*
      */
    def rightUnitorLeftInverse[A: Obj](using ((A * I) --> (A * I)) is Observable): Boolean = {
      IsoLaws.leftInverse(rightUnitor[A])
    }

    /** *ρ* ∘ *ρ*⁻¹ = *id*
      */
    def rightUnitorRightInverse[A: Obj](using (A --> A) is Observable): Boolean = {
      IsoLaws.rightInverse(rightUnitor[A])
    }

    /** *α*⁻¹ ∘ *α* = *id*
      */
    def associatorLeftInverse[A: Obj, B: Obj, C: Obj](
      using (((A * B) * C) --> ((A * B) * C)) is Observable
    ): Boolean = {
      IsoLaws.leftInverse(associator[A, B, C])
    }

    /** *α* ∘ *α*⁻¹ = *id*
      */
    def associatorRightInverse[A: Obj, B: Obj, C: Obj](
      using ((A * (B * C)) --> (A * (B * C))) is Observable
    ): Boolean = {
      IsoLaws.rightInverse(associator[A, B, C])
    }

    /** *f* ∘ *λ* = *λ* ∘ (*I* ⊘ *f*)
      */
    def leftUnitorNaturality[A: Obj, B: Obj](f: A --> B)(using ((I * A) --> B) is Observable): Boolean = {
      (leftUnitor[A].to >>> f) =?= (rmap[A, B, I](f) >>> leftUnitor[B].to)
    }

    /** *f* ∘ *ρ* = *ρ* ∘ (*f* ⦸ *I*)
      */
    def rightUnitorNaturality[A: Obj, B: Obj](f: A --> B)(using ((A * I) --> B) is Observable): Boolean = {
      (rightUnitor[A].to >>> f) =?= (lmap[A, B, I](f) >>> rightUnitor[B].to)
    }

    /** (*f* ⦸ (*C* ⊗ *D*)) ∘ *α* = *α* ∘ ((*f* ⦸ *C*) ⦸ *D*) */
    def associatorLeftNaturality[A: Obj, B: Obj, C: Obj, D: Obj](f: A --> B)(
      using (((A * C) * D) --> (B * (C * D))) is Observable
    ): Boolean = {
      (associator[A, C, D].to >>> lmap[A, B, C * D](f))
        =?= (lmap[A * C, B * C, D](lmap[A, B, C](f)) >>> associator[B, C, D].to)
    }

    /** (*C* ⊘ (*f* ⦸ *D*)) ∘ *α* = *α* ∘ ((*C* ⊘ *f*) ⦸ *D*) */
    def associatorMiddleNaturality[A: Obj, B: Obj, C: Obj, D: Obj](f: A --> B)(
      using (((C * A) * D) --> (C * (B * D))) is Observable
    ): Boolean = {
      (associator[C, A, D].to >>> rmap[A * D, B * D, C](lmap[A, B, D](f)))
        =?= (lmap[C * A, C * B, D](rmap[A, B, C](f)) >>> associator[C, B, D].to)
    }

    /** (*C* ⊘ (*D* ⊘ *f*)) ∘ *α* = *α* ∘ ((*C* ⊗ *D*) ⊘ *f*) */
    def associatorRightNaturality[A: Obj, B: Obj, C: Obj, D: Obj](f: A --> B)(
      using (((C * D) * A) --> (C * (D * B))) is Observable
    ): Boolean = {
      (associator[C, D, A].to >>> rmap[D * A, D * B, C](rmap[A, B, D](f)))
        =?= (rmap[A, B, C * D](f) >>> associator[C, D, B].to)
    }

    /** (*A* ⊘ *g*) ∘ (*λ* ⦸ *X*) = (*λ* ⦸ *Y*) ∘ ((*I* ⊗ *A*) ⊘ *g*), and likewise on the right: *λ* is central. */
    def leftUnitorCentrality[A: Obj, X: Obj, Y: Obj](g: X --> Y)(
      using (((I * A) * X) --> (A * Y)) is Observable,
      ((X * (I * A)) --> (Y * A)) is Observable,
    ): Boolean = {
      interchangesLeft(leftUnitor[A].to, g) && interchangesRight(leftUnitor[A].to, g)
    }

    /** (*A* ⊘ *g*) ∘ (*ρ* ⦸ *X*) = (*ρ* ⦸ *Y*) ∘ ((*A* ⊗ *I*) ⊘ *g*), and likewise on the right: *ρ* is central. */
    def rightUnitorCentrality[A: Obj, X: Obj, Y: Obj](g: X --> Y)(
      using (((A * I) * X) --> (A * Y)) is Observable,
      ((X * (A * I)) --> (Y * A)) is Observable,
    ): Boolean = {
      interchangesLeft(rightUnitor[A].to, g) && interchangesRight(rightUnitor[A].to, g)
    }

    /** ((*A* ⊗ (*B* ⊗ *C*)) ⊘ *g*) ∘ (*α* ⦸ *X*) = (*α* ⦸ *Y*) ∘ (((*A* ⊗ *B*) ⊗ *C*) ⊘ *g*), and likewise on the
      * right: *α* is central.
      */
    def associatorCentrality[A: Obj, B: Obj, C: Obj, X: Obj, Y: Obj](g: X --> Y)(
      using ((((A * B) * C) * X) --> ((A * (B * C)) * Y)) is Observable,
      ((X * ((A * B) * C)) --> (Y * (A * (B * C)))) is Observable,
    ): Boolean = {
      interchangesLeft(associator[A, B, C].to, g) && interchangesRight(associator[A, B, C].to, g)
    }

    /** (*A* ⊘ *λ*) ∘ *α* = *ρ* ⦸ *B* */
    def triangle[A: Obj, B: Obj](using (((A * I) * B) --> (A * B)) is Observable): Boolean = {
      (associator[A, I, B].to >>> rmap[I * B, B, A](leftUnitor[B].to))
        =?= lmap[A * I, A, B](rightUnitor[A].to)
    }

    /** (*A* ⊘ *α*) ∘ *α* ∘ (*α* ⦸ *D*) = *α* ∘ *α* */
    def pentagon[A: Obj, B: Obj, C: Obj, D: Obj](
      using ((((A * B) * C) * D) --> (A * (B * (C * D)))) is Observable
    ): Boolean = {
      val lhs = lmap[(A * B) * C, A * (B * C), D](associator[A, B, C].to) >>> associator[A, B * C, D].to >>>
        rmap[(B * C) * D, B * (C * D), A](associator[B, C, D].to)
      val rhs = associator[A * B, C, D].to >>> associator[A, B, C * D].to
      lhs =?= rhs
    }
  }
}

object Premonoidal {

  /** The premonoidal structures on a category **C**. */
  type On[C <: Category] = Premonoidal { val category: C }
}
