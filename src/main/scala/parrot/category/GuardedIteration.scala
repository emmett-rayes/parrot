package parrot
package category

/** A guarded iteration structure on a bistrong promonad *P* over a cocartesian category **M**.
  *
  * Represents a guarded iteration operator (Goncharov–Schröder–Rauch–Piróg), where
  *   - † is the iteration operator, defined for every step
  *
  * Some steps are guarded: they make progress whenever they continue. What progress is belongs to the instance, such
  * as consuming input. The operator is defined for every step, and its laws hold for the guarded ones. An [[Elgot]]
  * operator is the case in which every step is guarded.
  *
  * @see docs/TUTORIAL.md §19.7
  */
abstract class GuardedIteration(tracked val strong: StrongPromonad { val monoidal: Cocartesian }) extends caps.Pure {
  import strong.{monoidal, profunctor}
  import monoidal.+
  import profunctor.{P, >>>}
  import profunctor.arrows.-->
  import profunctor.category.{Obj, identity, --> as ==>}

  /** The iteration *p*†: *P*(*X*,*A*) of *p*: *P*(*X*,*A* + *X*).
    *
    * It runs *p*; on *A* it stops, and on *X* it runs *p* again.
    */
  def iterate[A: Obj, X: Obj](p: X --> (A + X)): X --> A

  /** Laws that any `GuardedIteration` operator must satisfy.
    *
    * These are the laws of a uniform Conway iteration operator, each for guarded steps.
    */
  object GuardedIterationLaws {
    private given TensorIsObj: [A: Obj, B: Obj] => ((A + B) is Obj) = monoidal.tensor.objects[A, B]

    /** *p*† = [*id*,*p*†] ∘ *p*
      *
      * Unrolling one iteration changes nothing.
      *
      * @note Holds for a guarded *p*. The premise is not checked.
      */
    def fixedPoint[A: Obj, X: Obj](p: X --> (A + X))(using (X --> A) is Observable): Boolean = {
      iterate(p) =?= (p >>> strong.left[X, A, A](iterate(p)) >>> profunctor.unit(monoidal.codiagonal[A]))
    }

    /** (*η*(*h* + *id*) ∘ *p*)† = *η*(*h*) ∘ *p*† for pure *h*: *A* → *B*
      *
      * Post-processing the result can be done inside the loop or after it.
      *
      * @note Holds for a guarded *p*. The premise is not checked.
      */
    def parameterNaturality[A: Obj, B: Obj, X: Obj](p: X --> (A + X), h: A ==> B)(
      using (X --> B) is Observable
    ): Boolean = {
      iterate(p >>> strong.right[A, B, X](profunctor.unit(h))) =?= (iterate(p) >>> profunctor.unit(h))
    }

    /** (*p* ∘ *η*(*g*))† = (*η*(*id* + *g*) ∘ *p*)† ∘ *η*(*g*) for pure *g*: *X* → *Y*
      *
      * A pure step at the start of each round can be rotated to the end.
      *
      * @note Holds for a guarded *p*. The premise is not checked.
      */
    def composition[A: Obj, X: Obj, Y: Obj](p: P[Y, A + X], g: X ==> Y)(
      using (X --> A) is Observable
    ): Boolean = {
      iterate[A, X](profunctor.unit(g) >>> p)
        =?= (profunctor.unit(g) >>> iterate[A, Y](p >>> profunctor.unit(monoidal.parallel(identity[A], g))))
    }

    /** ([*ι*₁,*g*] ∘ *f*)† = [*id*,([*ι*₁,*f*] ∘ *g*)†] ∘ *f* for *f*: *X* → *A* + *Y* and *g*: *Y* → *A* + *X*
      *
      * A loop that alternates two steps can start with either. [*ι*₁,*g*] runs *g* on the right and passes *A* through:
      * with effects, it is *η*([*ι*₁,*id*]) ∘ *τ*(*g*). [[composition]] is the special case of a pure *g*.
      *
      * @note Holds where both alternating loops are guarded. The premise is not checked.
      */
    def dinaturality[A: Obj, X: Obj, Y: Obj](f: P[X, A + Y], g: P[Y, A + X])(
      using (X --> A) is Observable
    ): Boolean = {
      val fg = f >>> strong.left[Y, A + X, A](g) >>>
        profunctor.unit(monoidal.copair(monoidal.inl[A, X], identity[A + X]))
      val gf = g >>> strong.left[X, A + Y, A](f) >>>
        profunctor.unit(monoidal.copair(monoidal.inl[A, Y], identity[A + Y]))
      iterate[A, X](fg) =?= (f >>> strong.left[Y, A, A](iterate[A, Y](gf)) >>> profunctor.unit(monoidal.codiagonal[A]))
    }

    /** (*p*†)† = (*η*([*id*,*ι*₂]) ∘ *p*)†
      *
      * A loop inside a loop over the same state is one loop.
      *
      * @note Holds for a *p* that is guarded in both of its ways to continue. The premise is not checked.
      */
    def doubleDagger[A: Obj, X: Obj](p: P[X, (A + X) + X])(
      using (X --> A) is Observable
    ): Boolean = {
      iterate[A, X](iterate[A + X, X](p))
        =?= iterate[A, X](p >>> profunctor.unit(monoidal.copair(identity[A + X], monoidal.inr[A, X])))
    }

    /** If *η*(*id* + *h*) ∘ *f* = *g* ∘ *η*(*h*) for pure *h*: *X* → *Y*, then *f*† = *g*† ∘ *η*(*h*).
      *
      * Loops related by a change of state representation compute the same thing.
      *
      * @note The premise is not checked: *g* must be built to satisfy it. Holds for guarded *f* and *g*.
      */
    def uniformity[A: Obj, X: Obj, Y: Obj](
      f: P[X, A + X],
      g: P[Y, A + Y],
      h: X ==> Y,
    )(using (X --> A) is Observable): Boolean = {
      iterate(f) =?= (profunctor.unit(h) >>> iterate(g))
    }

    /** If *p* = *p*′, then *p*† = *p*′†.
      *
      * @note The premise is not checked: *p*′ must be equal to *p* by construction.
      */
    def congruence[A: Obj, X: Obj](p: P[X, A + X], p2: P[X, A + X])(
      using (X --> A) is Observable
    ): Boolean = {
      iterate(p) =?= iterate(p2)
    }
  }
}

object GuardedIteration {

  /** The guarded iteration structures on a bistrong promonad with the strength *S*. */
  type On[S <: Bistrong] = GuardedIteration { val strong: S }
}
