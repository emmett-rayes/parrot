package parrot
package category

/** A left module over a monoidal category **M** on a category **C** (also called a left actegory).
  *
  * Represents a left module (**C**, ⊘), where
  *   - ⊘: **M** × **C** → **C** is the action bifunctor
  *   - *λ*: *I* ⊘ *A* ≅ *A* is the action left unitor
  *   - *α*: (*X* ⊗ *Y*) ⊘ *A* ≅ *X* ⊘ (*Y* ⊘ *A*) is the action associator
  */
abstract class Module(
  tracked val monoidal: Monoidal,
  tracked val category: Category,
  tracked val action: Bifunctor.Into[category.type] { val source1: monoidal.category.type; val source2: category.type },
) extends caps.Pure {
  import category.{Obj, -->, <->, >>>}
  import monoidal.category.{Obj as ObjM, --> as ==>}
  import monoidal.I
  import monoidal.`*`

  /** The action of **M** on **C**: *X* ⊘ *A*. */
  final type Action = action.F

  /** Infix alias for [[Action]]. */
  final type ~ = Action

  private given IIsObj: (I is ObjM) = monoidal.unit.evidence

  private given TensorIsObj: [X: ObjM, Y: ObjM] => ((X * Y) is ObjM) = monoidal.tensor.objects[X, Y]

  private given ActionIsObj: [X: ObjM, A: Obj] => ((X ~ A) is Obj) = action.objects[X, A]

  /** *λ*: *I* ⊘ *A* ≅ *A*
    */
  def leftUnitor[A: Obj]: (I ~ A) <-> A

  /** *α*: (*X* ⊗ *Y*) ⊘ *A* ≅ *X* ⊘ (*Y* ⊘ *A*)
    */
  def associator[X: ObjM, Y: ObjM, A: Obj]: ((X * Y) ~ A) <-> (X ~ (Y ~ A))

  /** The action on morphisms *g* ⊘ *f*. */
  final def act[X: ObjM, Y: ObjM, A: Obj, B: Obj](g: X ==> Y, f: A --> B): (X ~ A) --> (Y ~ B) = {
    action.bimap(g, f)
  }

  extension [X: ObjM, Y: ObjM](g: X ==> Y) {

    /** Infix extension for [[act]]. */
    final def ~~[A: Obj, B: Obj](f: A --> B): (X ~ A) --> (Y ~ B) = {
      act(g, f)
    }
  }

  /** Laws that any `Module` must satisfy. */
  object ModuleLaws {

    /** *λ*⁻¹ ∘ *λ* = *id*
      */
    def leftUnitorLeftInverse[A: Obj](using ((I ~ A) --> (I ~ A)) is Observable): Boolean = {
      category.IsoLaws.leftInverse(leftUnitor[A])
    }

    /** *λ* ∘ *λ*⁻¹ = *id*
      */
    def leftUnitorRightInverse[A: Obj](using (A --> A) is Observable): Boolean = {
      category.IsoLaws.rightInverse(leftUnitor[A])
    }

    /** *α*⁻¹ ∘ *α* = *id*
      */
    def associatorLeftInverse[X: ObjM, Y: ObjM, A: Obj](
      using (((X * Y) ~ A) --> ((X * Y) ~ A)) is Observable
    ): Boolean = {
      category.IsoLaws.leftInverse(associator[X, Y, A])
    }

    /** *α* ∘ *α*⁻¹ = *id*
      */
    def associatorRightInverse[X: ObjM, Y: ObjM, A: Obj](
      using ((X ~ (Y ~ A)) --> (X ~ (Y ~ A))) is Observable
    ): Boolean = {
      category.IsoLaws.rightInverse(associator[X, Y, A])
    }

    /** *f* ∘ *λ* = *λ* ∘ (*id* ⊘ *f*)
      */
    def leftUnitorNaturality[A: Obj, B: Obj](f: A --> B)(using ((I ~ A) --> B) is Observable): Boolean = {
      (leftUnitor[A].to >>> f) =?= ((monoidal.category.identity[I] ~~ f) >>> leftUnitor[B].to)
    }

    /** (*g* ⊘ (*h* ⊘ *f*)) ∘ *α* = *α* ∘ ((*g* ⊗ *h*) ⊘ *f*)
      */
    def associatorNaturality[X: ObjM, Y: ObjM, Z: ObjM, W: ObjM, A: Obj, B: Obj](
      g: X ==> Y,
      h: Z ==> W,
      f: A --> B,
    )(using (((X * Z) ~ A) --> (Y ~ (W ~ B))) is Observable): Boolean = {
      (associator[X, Z, A].to >>> (g ~~ (h ~~ f))) =?= ((monoidal.parallel(g, h) ~~ f) >>> associator[Y, W, B].to)
    }

    /** (*id* ⊘ *λ*) ∘ *α* = *ρ* ⊘ *id*
      */
    def triangle[X: ObjM, A: Obj](using (((X * I) ~ A) --> (X ~ A)) is Observable): Boolean = {
      (associator[X, I, A].to >>> (monoidal.category.identity[X] ~~ leftUnitor[A].to)) =?=
        (monoidal.rightUnitor[X].to ~~ category.identity[A])
    }

    /** (*id* ⊘ *α*) ∘ *α* ∘ (*αᴹ* ⊘ *id*) = *α* ∘ *α*
      */
    def pentagon[X: ObjM, Y: ObjM, Z: ObjM, A: Obj](
      using (((((X * Y) * Z) ~ A) --> (X ~ (Y ~ (Z ~ A)))) is Observable)
    ): Boolean = {
      val lhs = (monoidal.associator[X, Y, Z].to ~~ category.identity[A]) >>> associator[X, Y * Z, A].to >>>
        (monoidal.category.identity[X] ~~ associator[Y, Z, A].to)
      val rhs = associator[X * Y, Z, A].to >>> associator[X, Y, Z ~ A].to
      lhs =?= rhs
    }
  }
}

object Module {

  /** The left modules over a monoidal category **M**. */
  type Over[M <: Monoidal] = Module { val monoidal: M }

  /** Every monoidal category is canonically a left module over itself by its tensor bifunctor. */
  open class OfMonoidal(tracked override val monoidal: Monoidal)
      extends Module(monoidal, monoidal.category, monoidal.tensor) {
    import category.{Obj, <->}
    import monoidal.`*`
    import monoidal.category.{Obj as ObjM}

    def leftUnitor[A: Obj]: (monoidal.I ~ A) <-> A = {
      monoidal.leftUnitor[A]
    }

    def associator[X: ObjM, Y: ObjM, A: Obj]: ((X * Y) ~ A) <-> (X ~ (Y ~ A)) = {
      monoidal.associator[X, Y, A]
    }
  }
}
