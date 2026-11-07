package parrot
package category

/** A parameterized fixed-point structure on a bistrong promonad *P* over a cartesian category **M**.
  *
  * Represents a Conway operator (Bloom–Ésik; Hasegawa), where
  *   - †: is the fixed point operator.
  *
  * Conway operators are equivalent to traces for products. See [[Traced.OfConway]]. Conway operators are dual to Elgot
  * iteration. See [[Elgot]].
  */
abstract class Conway(tracked val strong: StrongPromonad { val monoidal: Cartesian }) extends caps.Pure {
  import strong.{monoidal, profunctor}
  import monoidal.`*`
  import profunctor.{P, >>>}
  import profunctor.arrows.-->
  import profunctor.category.{Obj, identity, --> as ==>}

  /** The fixed point *p*†: *P*(*A*,*X*) of *p*: *P*(*A* × *X*,*X*).
    *
    * It solves *x* = *p*(*a*,*x*) for *x*.
    */
  def fix[A: Obj, X: Obj](p: (A * X) --> X): A --> X

  /** Laws that any `Conway` operator must satisfy. */
  object ConwayLaws {
    private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = monoidal.tensor.objects[A, B]

    /** *p*† = *p* ∘ ⟨*id*,*p*†⟩
      *
      * Unfolding one step changes nothing.
      */
    def fixedPoint[A: Obj, X: Obj](p: (A * X) --> X)(using (A --> X) is Observable): Boolean = {
      fix(p) =?= (profunctor.unit(monoidal.diagonal[A]) >>> strong.left[A, X, A](fix(p)) >>> p)
    }

    /** (*p* ∘ *η*(*h* × *id*))† = *p*† ∘ *η*(*h*) for pure *h*: *A*₀ → *A*₁
      *
      * Pre-processing the parameter can be done inside the fixed point or before it.
      */
    def parameterNaturality[A0: Obj, A1: Obj, X: Obj](p: (A1 * X) --> X, h: A0 ==> A1)(
      using (A0 --> X) is Observable
    ): Boolean = {
      fix(strong.right[A0, A1, X](profunctor.unit(h)) >>> p) =?= (profunctor.unit(h) >>> fix(p))
    }

    /** (*η*(*g*) ∘ *f*)† = *η*(*g*) ∘ (*f* ∘ *η*(*id* × *g*))† for pure *g*: *Y* → *X*
      *
      * A pure step at the end of the body can be rotated to the start.
      */
    def composition[A: Obj, X: Obj, Y: Obj](f: P[A * X, Y], g: Y ==> X)(
      using (A --> X) is Observable
    ): Boolean = {
      fix[A, X](f >>> profunctor.unit(g))
        =?= (fix[A, Y](profunctor.unit(monoidal.parallel(identity[A], g)) >>> f) >>> profunctor.unit(g))
    }

    /** (*f* ∘ ⟨*π*₁,*g*⟩)† = *f* ∘ ⟨*id*,(*g* ∘ ⟨*π*₁,*f*⟩)†⟩ for *f*: *A* × *Y* → *X* and *g*: *A* × *X* → *Y*
      *
      * A fixed point of two arrows that feed each other can be taken through either. ⟨*π*₁,*g*⟩ keeps the parameter and
      * runs *g*: with effects, it is *τ*(*g*) ∘ *η*(⟨*π*₁,*id*⟩). [[composition]] is the special case of a pure *g*.
      */
    def dinaturality[A: Obj, X: Obj, Y: Obj](f: P[A * Y, X], g: P[A * X, Y])(
      using (A --> X) is Observable
    ): Boolean = {
      val keepG = profunctor.unit(monoidal.pair(monoidal.fst[A, X], identity[A * X])) >>>
        strong.left[A * X, Y, A](g)
      val keepF = profunctor.unit(monoidal.pair(monoidal.fst[A, Y], identity[A * Y])) >>>
        strong.left[A * Y, X, A](f)
      fix[A, X](keepG >>> f)
        =?= (profunctor.unit(monoidal.diagonal[A]) >>> strong.left[A, Y, A](fix[A, Y](keepF >>> g)) >>> f)
    }

    /** (*p*†)† = (*p* ∘ *η*(⟨*id*,*π*₂⟩))†
      *
      * A fixed point inside a fixed point over the same state is one fixed point.
      */
    def doubleDagger[A: Obj, X: Obj](p: P[(A * X) * X, X])(
      using (A --> X) is Observable
    ): Boolean = {
      fix[A, X](fix[A * X, X](p))
        =?= fix[A, X](profunctor.unit(monoidal.pair(identity[A * X], monoidal.snd[A, X])) >>> p)
    }

    /** If *g* ∘ *η*(*id* × *h*) = *η*(*h*) ∘ *f* for pure *h*: *X* → *Y*, then *η*(*h*) ∘ *f*† = *g*†.
      *
      * Fixed points related by a change of state representation are equal.
      *
      * @note The premise is not checked: *g* must be built to satisfy it.
      */
    def uniformity[A: Obj, X: Obj, Y: Obj](
      f: P[A * X, X],
      g: P[A * Y, Y],
      h: X ==> Y,
    )(using (A --> Y) is Observable): Boolean = {
      (fix(f) >>> profunctor.unit(h)) =?= fix(g)
    }

    /** If *p* = *p*′, then *p*† = *p*′†.
      *
      * @note The premise is not checked: *p*′ must be equal to *p* by construction.
      */
    def congruence[A: Obj, X: Obj](p: P[A * X, X], p2: P[A * X, X])(
      using (A --> X) is Observable
    ): Boolean = {
      fix(p) =?= fix(p2)
    }
  }
}

object Conway {

  /** The fixed-point structures on a bistrong promonad with the strength *S*. */
  type On[S <: Bistrong] = Conway { val strong: S }

  /** The fixed point on *P*ᵒᵖ of an Elgot operator *E* on *P*: iteration read backwards.
    *
    * The products of **C**ᵒᵖ are the coproducts of **C**, so a step *P*(*X*,*A* + *X*) is an arrow *P*ᵒᵖ(*A* ×
    * *X*,*X*), and its iteration *P*(*X*,*A*) is the fixed point *P*ᵒᵖ(*A*,*X*).
    */
  open class OfElgot(tracked val elgot: Elgot)
      extends Conway(Bistrong.Op(elgot.strong)) {
    import strong.{monoidal, profunctor}
    import monoidal.`*`
    import profunctor.P
    import profunctor.arrows.-->
    import profunctor.category.Obj

    def fix[A: Obj, X: Obj](p: (A * X) --> X): (A --> X) = {
      elgot.iterate[A, X](p)
    }
  }

  /** The fixed point of a trace *T* on products: *p*† = *tr*(*η*(Δ) ∘ *p*). */
  open class OfTraced(
    tracked val traced: Traced.On[Freyd.On[StrongPromonad { val monoidal: Cartesian }]],
  ) extends Conway(traced.premonoidal.strong) {
    import strong.{monoidal, profunctor}
    import monoidal.`*`
    import profunctor.{P, >>>}
    import profunctor.arrows.-->
    import profunctor.category.Obj

    private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = monoidal.tensor.objects[A, B]

    def fix[A: Obj, X: Obj](p: (A * X) --> X): (A --> X) = {
      traced.trace[A, X, X](p >>> profunctor.unit(monoidal.diagonal[X]))
    }
  }
}
