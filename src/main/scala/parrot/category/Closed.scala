package parrot
package category

/** A closed structure on a monoidal category.
  *
  * Represents a monoidal closed category, where
  *   - *A* ⇒ *B*, also written as the exponential *B*ᴬ, is the internal hom object of *A* and *B*
  *   - *ev*: (*A* ⇒ *B*) ⊗ *A* → *B* is evaluation
  *   - Λ(*f*): *C* → (*A* ⇒ *B*) is the curried form of *f*: *C* ⊗ *A* → *B*
  */
abstract class Closed(tracked val M: Monoidal) extends caps.Pure {
  import M.{`*`, ***, given}
  import M.K.{Obj, -->, >>>}

  /** The internal hom *A* ⇒ *B*. */
  type Exp[A, B]

  /** Infix alias for [[Exp]]. */
  final type `^`[B, A] = Exp[A, B]

  /** Internal homs of objects are objects. */
  def objects[A: Obj, B: Obj]: (B `^` A) is Obj

  /** Evidence that internal homs of objects are objects, for clients of the structure. */
  given ExpIsObj: [A: Obj, B: Obj] => ((B `^` A) is Obj) = objects[A, B]

  /** Evaluation *ev*: (*A* ⇒ *B*) ⊗ *A* → *B*. */
  def eval[A: Obj, B: Obj]: ((B `^` A) * A) --> B

  /** Currying Λ: **K**(*C* ⊗ *A*,*B*) → **K**(*C*,*A* ⇒ *B*).
    *
    * This is the unique morphism such that *ev* ∘ (Λ(*f*) ⊗ *id*) = *f*.
    */
  def curry[A: Obj, B: Obj, C: Obj](f: (C * A) --> B): C --> (B `^` A)

  /** Uncurrying: *g* ↦ *ev* ∘ (*g* ⊗ *id*). */
  final def uncurry[A: Obj, B: Obj, C: Obj](g: C --> (B `^` A)): (C * A) --> B = {
    (g *** M.K.identity[A]) >>> eval[A, B]
  }

  /** The internal hom as a profunctor ⇒: **K**ᵒᵖ × **K** → **K**. */
  final lazy val internalHom: Closed.InternalHom { val C: Closed.this.type } = Closed.InternalHom(this)

  /** Laws that any `Closed` structure must satisfy: currying and uncurrying are inverse. */
  object ClosedLaws {

    /** *ev* ∘ (Λ(*f*) ⊗ *id*) = *f*
      */
    def beta[A: Obj, B: Obj, C: Obj](f: (C * A) --> B)(
      using ((C * A) --> B) is Observable
    ): Boolean = {
      uncurry(curry(f)) =?= f
    }

    /** Λ(*ev* ∘ (*g* ⊗ *id*)) = *g* */
    def eta[A: Obj, B: Obj, C: Obj](g: C --> (B `^` A))(
      using (C --> (B `^` A)) is Observable
    ): Boolean = {
      curry(uncurry(g)) =?= g
    }

    /** If *f* = *f*′, then Λ(*f*) = Λ(*f*′).
      *
      * @note The premise is not checked: *f*′ must be equal to *f* by construction.
      */
    def curryCongruence[A: Obj, B: Obj, C: Obj](f: (C * A) --> B, f2: (C * A) --> B)(
      using (C --> (B `^` A)) is Observable
    ): Boolean = {
      curry(f) =?= curry(f2)
    }
  }
}

object Closed {

  /** The internal hom ⇒: **K**ᵒᵖ × **K** → **K** of a closed structure, as a profunctor.
    *
    * Represents a profunctor, where
    *   - *A* ⇒ *B* is the object part
    *   - *f* ⇒ *g* = Λ(*g* ∘ *ev* ∘ (*id* ⊗ *f*)): (*A*₁ ⇒ *B*₁) → (*A*₂ ⇒ *B*₂) is the morphism part
    *
    * @note The morphism part is determined by evaluation and currying, so the laws of the profunctor follow from the
    *   laws `beta` and `eta` of [[Closed]].
    */
  final class InternalHom(tracked val C: Closed) extends Profunctor(C.M.K, C.M.K) {
    import C.M.{***, given}
    import C.M.K.{Obj, -->, >>>}
    import C.given

    type Self = C.Exp

    def objects[A: Obj, B: Obj]: P[A, B] is Obj = {
      C.objects[A, B]
    }

    def bimap[A1: Obj, B1: Obj, A2: Obj, B2: Obj](f: A2 --> A1, g: B1 --> B2): P[A1, B1] --> P[A2, B2] = {
      C.curry((C.M.K.identity[P[A1, B1]] *** f) >>> C.eval[A1, B1] >>> g)
    }
  }
}
