package parrot
package category

/** A closed structure on a bistrong promonad *P* over **C**.
  *
  * Represents a closed Freyd category (Power–Thielecke), where
  *   - *A* ⇒ *B*, the Kleisli exponential, is an object of **C**
  *   - *ev*: *P*((*A* ⇒ *B*) ⊗ *A*,*B*) is evaluation
  *   - Λ(*p*): *X* → (*A* ⇒ *B*) is the curried form of *p*: *P*(*X* ⊗ *A*,*B*)
  *
  * Currying is a bijection *P*(*X* ⊗ *A*,*B*) ≅ **C**(*X*,*A* ⇒ *B*): a curried arrow is pure, and runs only when it is
  * evaluated. Over a hom promonad, this is a [[Closed]] structure.
  *
  * @see docs/TUTORIAL.md §17.4
  */
abstract class ClosedFreyd(tracked val strong: StrongPromonad) extends caps.Pure {
  import strong.monoidal.{`*`, ***}
  import strong.profunctor
  import profunctor.{>>>, arrows}
  import arrows.-->
  import profunctor.category.{Obj, identity, --> as ==>}

  /** The Kleisli exponential *A* ⇒ *B*. */
  type Exp[A, B]

  /** Infix alias for [[Exp]]. */
  final type `^`[B, A] = Exp[A, B]

  /** Kleisli exponentials of objects are objects. */
  def objects[A: Obj, B: Obj]: (B `^` A) is Obj

  /** Evaluation *ev*: *P*((*A* ⇒ *B*) ⊗ *A*,*B*). */
  def eval[A: Obj, B: Obj]: ((B `^` A) * A) --> B

  /** Currying Λ: *P*(*X* ⊗ *A*,*B*) → **C**(*X*,*A* ⇒ *B*).
    *
    * This is the unique morphism such that *ev* ∘ *η*(Λ(*p*) ⊗ *id*) = *p*.
    */
  def curry[A: Obj, B: Obj, X: Obj](p: (X * A) --> B): X ==> (B `^` A)

  private given ExpIsObj: [A: Obj, B: Obj] => ((B `^` A) is Obj)  = objects[A, B]
  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = strong.monoidal.tensor.objects[A, B]

  /** Uncurrying: *g* ↦ *ev* ∘ *η*(*g* ⊗ *id*). */
  def uncurry[A: Obj, B: Obj, X: Obj](g: X ==> (B `^` A)): (X * A) --> B = {
    profunctor.unit(g *** identity[A]) >>> eval[A, B]
  }

  /** Laws that any `ClosedFreyd` structure must satisfy: currying and uncurrying are inverse. */
  object ClosedFreydLaws {

    /** *ev* ∘ *η*(Λ(*p*) ⊗ *id*) = *p*
      */
    def beta[A: Obj, B: Obj, X: Obj](p: (X * A) --> B)(using ((X * A) --> B) is Observable): Boolean = {
      uncurry(curry(p)) =?= p
    }

    /** Λ(*ev* ∘ *η*(*g* ⊗ *id*)) = *g* */
    def eta[A: Obj, B: Obj, X: Obj](g: X ==> (B `^` A))(using (X ==> (B `^` A)) is Observable): Boolean = {
      curry(uncurry(g)) =?= g
    }

    /** *uncurry*(*g*) = *ev* ∘ *η*(*g* ⊗ *id*)
      */
    def uncurryIsEval[A: Obj, B: Obj, X: Obj](g: X ==> (B `^` A))(using ((X * A) --> B) is Observable): Boolean = {
      uncurry(g) =?= (profunctor.unit(g *** identity[A]) >>> eval[A, B])
    }

    /** If *p* = *p*′, then Λ(*p*) = Λ(*p*′).
      *
      * @note The premise is not checked: *p*′ must be equal to *p* by construction.
      */
    def curryCongruence[A: Obj, B: Obj, X: Obj](p: (X * A) --> B, p2: (X * A) --> B)(
      using (X ==> (B `^` A)) is Observable
    ): Boolean = {
      curry(p) =?= curry(p2)
    }
  }
}

object ClosedFreyd {

  /** The closed structures on a bistrong promonad *P*. */
  type On[P <: StrongPromonad] = ClosedFreyd { val strong: P }
}
