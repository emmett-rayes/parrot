package parrot
package category

/** A monoidal structure on a category **C**.
  *
  * Represents a monoidal category (**C**, ⊗, *I*), where
  *   - ⊗: **C** × **C** → **C** is the tensor bifunctor
  *   - *I* is the unit object
  *   - *λ*: *I* ⊗ *A* ≅ *A* is the left unitor
  *   - *ρ*: *A* ⊗ *I* ≅ *A* is the right unitor
  *   - *α*: (*A* ⊗ *B*) ⊗ *C* ≅ *A* ⊗ (*B* ⊗ *C*) is the associator
  */
abstract class Monoidal(
  tracked val category: Category,
  tracked val unit: category.Object,
  tracked val tensor: Endobifunctor.On[category.type],
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

  /** *λ*: *I* ⊗ *A* ≅ *A*
    */
  def leftUnitor[A: Obj]: (I * A) <-> A

  /** *ρ*: *A* ⊗ *I* ≅ *A*
    */
  def rightUnitor[A: Obj]: (A * I) <-> A

  /** *α*: (*A* ⊗ *B*) ⊗ *C* ≅ *A* ⊗ (*B* ⊗ *C*)
    */
  def associator[A: Obj, B: Obj, C: Obj]: ((A * B) * C) <-> (A * (B * C))

  /** The tensor of morphisms *f* ⊗ *g*. */
  final def parallel[A: Obj, B: Obj, C: Obj, D: Obj](f: A --> B, g: C --> D): (A * C) --> (B * D) = {
    tensor.bimap(f, g)
  }

  extension [A: Obj, B: Obj](f: A --> B)
    /** Infix extension for [[parallel]]. */
    final def ***[C: Obj, D: Obj](g: C --> D): (A * C) --> (B * D) = {
      parallel(f, g)
    }

  /** Laws that any `Monoidal` structure must satisfy. */
  object MonoidalLaws {
    import category.IsoLaws

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

    /** *f* ∘ *λ* = *λ* ∘ (*id* ⊗ *f*)
      */
    def leftUnitorNaturality[A: Obj, B: Obj](f: A --> B)(using ((I * A) --> B) is Observable): Boolean = {
      (leftUnitor[A].to >>> f) =?= ((category.identity[I] *** f) >>> leftUnitor[B].to)
    }

    /** *f* ∘ *ρ* = *ρ* ∘ (*f* ⊗ *id*)
      */
    def rightUnitorNaturality[A: Obj, B: Obj](f: A --> B)(using ((A * I) --> B) is Observable): Boolean = {
      (rightUnitor[A].to >>> f) =?= ((f *** category.identity[I]) >>> rightUnitor[B].to)
    }

    /** (*f* ⊗ (*g* ⊗ *h*)) ∘ *α* = *α* ∘ ((*f* ⊗ *g*) ⊗ *h*) */
    def associatorNaturality[A: Obj, B: Obj, C: Obj, D: Obj, E: Obj, F: Obj](
      f: A --> B,
      g: C --> D,
      h: E --> F,
    )(using (((A * C) * E) --> (B * (D * F))) is Observable): Boolean = {
      (associator[A, C, E].to >>> (f *** (g *** h))) =?= (((f *** g) *** h) >>> associator[B, D, F].to)
    }

    /** (*id* ⊗ *λ*) ∘ *α* = *ρ* ⊗ *id* */
    def triangle[A: Obj, B: Obj](using (((A * I) * B) --> (A * B)) is Observable): Boolean = {
      (associator[A, I, B].to >>> (category.identity[A] *** leftUnitor[B].to))
        =?= (rightUnitor[A].to *** category.identity[B])
    }

    /** (*id* ⊗ *α*) ∘ *α* ∘ (*α* ⊗ *id*) = *α* ∘ *α* */
    def pentagon[A: Obj, B: Obj, C: Obj, D: Obj](
      using ((((A * B) * C) * D) --> (A * (B * (C * D)))) is Observable
    ): Boolean = {
      val lhs = (associator[A, B, C].to *** category.identity[D]) >>> associator[A, B * C, D].to >>>
        (category.identity[A] *** associator[B, C, D].to)
      val rhs = associator[A * B, C, D].to >>> associator[A, B, C * D].to
      lhs =?= rhs
    }
  }
}

object Monoidal {

  /** The monoidal structures on a category **C**. */
  type On[C <: Category] = Monoidal { val category: C }
}
