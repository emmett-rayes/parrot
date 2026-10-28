package parrot
package category

/** A closed structure on a monoidal category: internal homs, the categorical form of function types.
  *
  * Represents a monoidal closed category, where
  *   - *A* ⇒ *B*, also written as the exponential *B*ᴬ, is the internal hom, an object
  *   - *ev*: (*A* ⇒ *B*) ⊗ *A* → *B* is evaluation
  *   - Λ(*f*): *C* → (*A* ⇒ *B*) is the curried form of *f*: *C* ⊗ *A* → *B*, the unique morphism with *ev* ∘ (Λ(*f*) ⊗
  *     *id*) = *f*
  */
abstract class Closed(tracked val M: Monoidal) extends caps.Pure {
  import M.{*, given}
  import M.K.{Obj, -->, >>>}

  /** The internal hom *A* ⇒ *B*. */
  type Exp[A, B]

  /** Infix alias for [[Exp]], in the order of the exponential *B*ᴬ = *A* ⇒ *B*. */
  final type ^[B, A] = Exp[A, B]

  /** Internal homs of objects are objects. */
  def objects[A: Obj, B: Obj]: (B ^ A) is Obj

  /** Evidence that internal homs of objects are objects, for clients of the structure. */
  given ExpIsObj: [A: Obj, B: Obj] => ((B ^ A) is Obj) = objects[A, B]

  /** Evaluation *ev*: (*A* ⇒ *B*) ⊗ *A* → *B*. */
  def eval[A: Obj, B: Obj]: ((B ^ A) * A) --> B

  /** Currying Λ: **K**(*C* ⊗ *A*,*B*) → **K**(*C*,*A* ⇒ *B*). */
  def curry[A: Obj, B: Obj, C: Obj](f: (C * A) --> B): C --> (B ^ A)

  /** Uncurrying: *g* ↦ *ev* ∘ (*g* ⊗ *id*). */
  final def uncurry[A: Obj, B: Obj, C: Obj](g: C --> (B ^ A)): (C * A) --> B = {
    (g *** M.K.identity[A]) >>> eval[A, B]
  }

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
    def eta[A: Obj, B: Obj, C: Obj](g: C --> (B ^ A))(
      using (C --> (B ^ A)) is Observable
    ): Boolean = {
      curry(uncurry(g)) =?= g
    }

    /** If *f* = *f*′, then Λ(*f*) = Λ(*f*′).
      *
      * @note The premise is not checked: *f*′ must be equal to *f* by construction.
      */
    def curryCongruence[A: Obj, B: Obj, C: Obj](f: (C * A) --> B, f2: (C * A) --> B)(
      using (C --> (B ^ A)) is Observable
    ): Boolean = {
      curry(f) =?= curry(f2)
    }
  }
}
