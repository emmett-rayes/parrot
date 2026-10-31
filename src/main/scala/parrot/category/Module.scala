package parrot
package category

/** A left module over a monoidal category **M** on a category **K** (also called a left actegory).
  *
  * Represents a left module (**K**, ⊘), where
  *   - ⊘: **M** × **K** → **K** is the action bifunctor
  *   - *λ*: *I* ⊘ *A* ≅ *A* is the action left unitor
  *   - *α*: (*X* ⊗ *Y*) ⊘ *A* ≅ *X* ⊘ (*Y* ⊘ *A*) is the action associator
  */
abstract class Module(
  tracked val K: Category,
  tracked val M: Monoidal,
  tracked val T: Bifunctor { val C1: M.K.type; val C2: K.type; val D: K.type },
) extends caps.Pure {
  import K.{Obj, -->, <->, >>>}
  import M.K.{Obj as ObjM, --> as ==>}
  import M.I
  import M.`*`

  /** The action of **M** on **K**: *X* ⊘ *A*. */
  final type Action = T.F

  /** Infix alias for [[Action]]. */
  final type ~ = Action

  /** Evidence that actions of objects are objects in **K**. */
  given actionIsObj: [X: ObjM, A: Obj] => ((X ~ A) is Obj) = T.objects[X, A]

  /** *λ*: *I* ⊘ *A* ≅ *A*
    */
  def leftUnitor[A: Obj]: (I ~ A) <-> A

  /** *α*: (*X* ⊗ *Y*) ⊘ *A* ≅ *X* ⊘ (*Y* ⊘ *A*)
    */
  def associator[X: ObjM, Y: ObjM, A: Obj]: ((X * Y) ~ A) <-> (X ~ (Y ~ A))

  /** The action on morphisms *g* ⊘ *f*. */
  final def act[X: ObjM, Y: ObjM, A: Obj, B: Obj](g: X ==> Y, f: A --> B): (X ~ A) --> (Y ~ B) = {
    T.bimap(g, f)
  }

  extension [X: ObjM, Y: ObjM](g: X ==> Y) {

    /** Infix extension for [[act]]. */
    final def ~~[A: Obj, B: Obj](f: A --> B): (X ~ A) --> (Y ~ B) = {
      act(g, f)
    }
  }

  /** Laws that any `Module` must satisfy. */
  object ModuleLaws {

    /** *λ*⁻¹ ∘ *λ* = *id* and *λ* ∘ *λ*⁻¹ = *id*
      */
    def leftUnitorIsomorphism[A: Obj](using ((I ~ A) --> (I ~ A)) is Observable, (A --> A) is Observable): Boolean = {
      K.IsoLaws.isomorphism(leftUnitor[A])
    }

    /** *α*⁻¹ ∘ *α* = *id* and *α* ∘ *α*⁻¹ = *id*
      */
    def associatorIsomorphism[X: ObjM, Y: ObjM, A: Obj](
      using
      (((X * Y) ~ A) --> ((X * Y) ~ A)) is Observable,
      ((X ~ (Y ~ A)) --> (X ~ (Y ~ A))) is Observable,
    ): Boolean = {
      K.IsoLaws.isomorphism(associator[X, Y, A])
    }

    /** *f* ∘ *λ* = *λ* ∘ (*id* ⊘ *f*)
      */
    def leftUnitorNaturality[A: Obj, B: Obj](f: A --> B)(using ((I ~ A) --> B) is Observable): Boolean = {
      (leftUnitor[A].to >>> f) =?= ((M.K.identity[I] ~~ f) >>> leftUnitor[B].to)
    }

    /** (*g* ⊘ (*h* ⊘ *f*)) ∘ *α* = *α* ∘ ((*g* ⊗ *h*) ⊘ *f*)
      */
    def associatorNaturality[X: ObjM, Y: ObjM, Z: ObjM, W: ObjM, A: Obj, B: Obj](
      g: X ==> Y,
      h: Z ==> W,
      f: A --> B,
    )(using (((X * Z) ~ A) --> (Y ~ (W ~ B))) is Observable): Boolean = {
      (associator[X, Z, A].to >>> (g ~~ (h ~~ f))) =?= ((M.tensor(g, h) ~~ f) >>> associator[Y, W, B].to)
    }

    /** (*id* ⊘ *λ*) ∘ *α* = *ρ* ⊘ *id*
      */
    def triangle[X: ObjM, A: Obj](using (((X * I) ~ A) --> (X ~ A)) is Observable): Boolean = {
      (associator[X, I, A].to >>> (M.K.identity[X] ~~ leftUnitor[A].to)) =?= (M.rightUnitor[X].to ~~ K.identity[A])
    }

    /** (*id* ⊘ *α*) ∘ *α* ∘ (*αᴹ* ⊘ *id*) = *α* ∘ *α*
      */
    def pentagon[X: ObjM, Y: ObjM, Z: ObjM, A: Obj](
      using (((((X * Y) * Z) ~ A) --> (X ~ (Y ~ (Z ~ A)))) is Observable)
    ): Boolean = {
      val lhs = (M.associator[X, Y, Z].to ~~ K.identity[A]) >>> associator[X, Y * Z, A].to >>>
        (M.K.identity[X] ~~ associator[Y, Z, A].to)
      val rhs = associator[X * Y, Z, A].to >>> associator[X, Y, Z ~ A].to
      lhs =?= rhs
    }
  }
}

object Module {

  /** Every monoidal category is canonically a left module over itself by its tensor bifunctor. */
  open class OfMonoidal(tracked override val M: Monoidal) extends Module(M.K, M, M.T) {
    import K.{Obj, <->}
    import M.`*`
    import M.K.{Obj as ObjM}

    def leftUnitor[A: Obj]: (M.I ~ A) <-> A = {
      M.leftUnitor[A]
    }

    def associator[X: ObjM, Y: ObjM, A: Obj]: ((X * Y) ~ A) <-> (X ~ (Y ~ A)) = {
      M.associator[X, Y, A]
    }
  }
}
