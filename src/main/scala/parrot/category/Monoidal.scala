package parrot
package category

/** A monoidal structure on a category **K**.
  *
  * Represents a monoidal category (**K**, ⊗, *I*), where
  *   - ⊗: **K** × **K** → **K** is the tensor bifunctor
  *   - *I* is the unit object
  *   - *λ*: *I* ⊗ *A* ≅ *A* is the left unitor
  *   - *ρ*: *A* ⊗ *I* ≅ *A* is the right unitor
  *   - *α*: (*A* ⊗ *B*) ⊗ *C* ≅ *A* ⊗ (*B* ⊗ *C*) is the associator
  */
abstract class Monoidal(
  tracked val K: Category,
  tracked val U: K.Obj,
  tracked val T: Bifunctor { val C1: K.type; val C2: K.type; val D: K.type },
) extends caps.Pure {
  import K.{Obj, -->, <->, >>>}

  /** The tensor of objects *A* ⊗ *B*. */
  final type Tensor = T.F

  /** Infix alias for [[Tensor]]. */
  final type * = Tensor

  /** The unit object *I*. */
  final type I = U.Self

  /** Evidence that *I* is an object, for clients of the structure. */
  given IIsObj: (I is Obj) = U

  /** Evidence that tensors of objects are objects, for clients of the structure. */
  given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = T.objects[A, B]

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
  final def tensor[A: Obj, B: Obj, C: Obj, D: Obj](f: A --> B, g: C --> D): (A * C) --> (B * D) = {
    T.bimap(f, g)
  }

  extension [A: Obj, B: Obj](f: A --> B)
    /** Infix form of [[tensor]]: *f* ⊗ *g*. */
    final def ***[C: Obj, D: Obj](g: C --> D): (A * C) --> (B * D) = {
      tensor(f, g)
    }

  /** Laws that any `Monoidal` structure must satisfy. */
  object MonoidalLaws {

    /** *λ*⁻¹ ∘ *λ* = *id* and *λ* ∘ *λ*⁻¹ = *id*
      */
    def leftUnitorIsomorphism[A: Obj](using ((I * A) --> (I * A)) is Observable, (A --> A) is Observable): Boolean = {
      K.IsoLaws.isomorphism(leftUnitor[A])
    }

    /** *ρ*⁻¹ ∘ *ρ* = *id* and *ρ* ∘ *ρ*⁻¹ = *id*
      */
    def rightUnitorIsomorphism[A: Obj](using ((A * I) --> (A * I)) is Observable, (A --> A) is Observable): Boolean = {
      K.IsoLaws.isomorphism(rightUnitor[A])
    }

    /** *α*⁻¹ ∘ *α* = *id* and *α* ∘ *α*⁻¹ = *id*
      */
    def associatorIsomorphism[A: Obj, B: Obj, C: Obj](
      using
      (((A * B) * C) --> ((A * B) * C)) is Observable,
      ((A * (B * C)) --> (A * (B * C))) is Observable,
    ): Boolean = {
      K.IsoLaws.isomorphism(associator[A, B, C])
    }

    /** *f* ∘ *λ* = *λ* ∘ (*id* ⊗ *f*)
      */
    def leftUnitorNaturality[A: Obj, B: Obj](f: A --> B)(using ((I * A) --> B) is Observable): Boolean = {
      (leftUnitor[A].to >>> f) =?= ((K.identity[I] *** f) >>> leftUnitor[B].to)
    }

    /** *f* ∘ *ρ* = *ρ* ∘ (*f* ⊗ *id*)
      */
    def rightUnitorNaturality[A: Obj, B: Obj](f: A --> B)(using ((A * I) --> B) is Observable): Boolean = {
      (rightUnitor[A].to >>> f) =?= ((f *** K.identity[I]) >>> rightUnitor[B].to)
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
      (associator[A, I, B].to >>> (K.identity[A] *** leftUnitor[B].to)) =?= (rightUnitor[A].to *** K.identity[B])
    }

    /** (*id* ⊗ *α*) ∘ *α* ∘ (*α* ⊗ *id*) = *α* ∘ *α* */
    def pentagon[A: Obj, B: Obj, C: Obj, D: Obj](
      using ((((A * B) * C) * D) --> (A * (B * (C * D)))) is Observable
    ): Boolean = {
      val lhs = (associator[A, B, C].to *** K.identity[D]) >>> associator[A, B * C, D].to >>>
        (K.identity[A] *** associator[B, C, D].to)
      val rhs = associator[A * B, C, D].to >>> associator[A, B, C * D].to
      lhs =?= rhs
    }
  }
}
