package parrot
package category

/** A closed structure on a monoidal category.
  *
  * Represents a monoidal closed category, where
  *   - *A* ⇒ *B*, also written as the exponential *B*ᴬ, is the internal hom object of *A* and *B*
  *   - *ev*: (*A* ⇒ *B*) ⊗ *A* → *B* is evaluation
  *   - Λ(*f*): *C* → (*A* ⇒ *B*) is the curried form of *f*: *C* ⊗ *A* → *B*
  */
abstract class Closed(tracked val monoidal: Monoidal) extends caps.Pure {
  import monoidal.{`*`, ***}
  import monoidal.category.{Obj, -->, >>>}

  /** The internal hom *A* ⇒ *B*. */
  type Exp[A, B]

  /** Infix alias for [[Exp]]. */
  final type `^`[B, A] = Exp[A, B]

  /** Internal homs of objects are objects. */
  def objects[A: Obj, B: Obj]: (B `^` A) is Obj

  private given ExpIsObj: [A: Obj, B: Obj] => ((B `^` A) is Obj) = objects[A, B]

  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = monoidal.tensor.objects[A, B]

  /** Evaluation *ev*: (*A* ⇒ *B*) ⊗ *A* → *B*. */
  def eval[A: Obj, B: Obj]: ((B `^` A) * A) --> B

  /** Currying Λ: **K**(*C* ⊗ *A*,*B*) → **K**(*C*,*A* ⇒ *B*).
    *
    * This is the unique morphism such that *ev* ∘ (Λ(*f*) ⊗ *id*) = *f*.
    */
  def curry[A: Obj, B: Obj, C: Obj](f: (C * A) --> B): C --> (B `^` A)

  /** Uncurrying: *g* ↦ *ev* ∘ (*g* ⊗ *id*). */
  final def uncurry[A: Obj, B: Obj, C: Obj](g: C --> (B `^` A)): (C * A) --> B = {
    (g *** monoidal.category.identity[A]) >>> eval[A, B]
  }

  /** The internal hom as a profunctor ⇒: **K**ᵒᵖ × **K** → **K**. */
  final lazy val internalHom: Closed.InternalHom { val closed: Closed.this.type } = Closed.InternalHom(this)

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

  /** The internal hom ⇒: **K**ᵒᵖ × **K** → **K** of a closed structure, as an endoprofunctor.
    *
    * Represents a profunctor, where
    *   - *A* ⇒ *B* is the object part
    *   - *f* ⇒ *g* = Λ(*g* ∘ *ev* ∘ (*id* ⊗ *f*)): (*A*₁ ⇒ *B*₁) → (*A*₂ ⇒ *B*₂) is the morphism part
    *
    * @note The morphism part is determined by evaluation and currying, so the laws of the profunctor follow from the
    *   laws `beta` and `eta` of [[Closed]].
    */
  final class InternalHom(tracked val closed: Closed)
      extends Endoprofunctor(closed.monoidal.category, closed.monoidal.category) {
    import closed.monoidal.{`*`, ***}
    import closed.monoidal.category.{Obj, -->, >>>}

    type Self = closed.Exp

    private given PIsObj: [A: Obj, B: Obj] => (P[A, B] is Obj) = closed.objects[A, B]

    private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = closed.monoidal.tensor.objects[A, B]

    def objects[A: Obj, B: Obj]: P[A, B] is Obj = {
      closed.objects[A, B]
    }

    def bimap[A1: Obj, A2: Obj, B1: Obj, B2: Obj](f: B1 --> A1, g: A2 --> B2): P[A1, A2] --> P[B1, B2] = {
      closed.curry((closed.monoidal.category.identity[P[A1, A2]] *** f) >>> closed.eval[A1, A2] >>> g)
    }
  }
}
