package parrot
package category

/** An iteration structure on a bistrong promonad *P* over a cocartesian category **M**.
  *
  * Represents an Elgot operator (Elgot; Bloom–Ésik), where
  *   - †: is the iteration operator.
  *
  * Elgot operators are equivalent to traces for coproducts. See [[Traced.OfElgot]]. Elgot operators are dual to Conway
  * fixed points. See [[Conway]].
  */
abstract class Elgot(tracked val strong: StrongPromonad { val monoidal: Cocartesian }) extends caps.Pure {
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

  /** Laws that any `Elgot` operator must satisfy. */
  object ElgotLaws {
    private given TensorIsObj: [A: Obj, B: Obj] => ((A + B) is Obj) = monoidal.tensor.objects[A, B]

    /** *p*† = [*id*,*p*†] ∘ *p*
      *
      * Unrolling one iteration changes nothing.
      */
    def fixedPoint[A: Obj, X: Obj](p: X --> (A + X))(using (X --> A) is Observable): Boolean = {
      iterate(p) =?= (p >>> strong.left[X, A, A](iterate(p)) >>> profunctor.unit(monoidal.codiagonal[A]))
    }

    /** (*η*(*h* + *id*) ∘ *p*)† = *η*(*h*) ∘ *p*† for pure *h*: *A* → *B*
      *
      * Post-processing the result can be done inside the loop or after it.
      */
    def parameterNaturality[A: Obj, B: Obj, X: Obj](p: X --> (A + X), h: A ==> B)(
      using (X --> B) is Observable
    ): Boolean = {
      iterate(p >>> strong.right[A, B, X](profunctor.unit(h))) =?= (iterate(p) >>> profunctor.unit(h))
    }

    /** (*p* ∘ *η*(*g*))† = (*η*(*id* + *g*) ∘ *p*)† ∘ *η*(*g*) for pure *g*: *X* → *Y*
      *
      * A pure step at the start of each round can be rotated to the end.
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
      * @note The premise is not checked: *g* must be built to satisfy it.
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

object Elgot {

  /** The iteration structures on a bistrong promonad with the strength *S*. */
  type On[S <: Bistrong] = Elgot { val strong: S }

  /** The iteration on *P*ᵒᵖ of a Conway operator *C* on *P*: fixed points read backwards. */
  open class OfConway(tracked val conway: Conway)
      extends Elgot(Bistrong.Op(conway.strong)) {
    import strong.{monoidal, profunctor}
    import monoidal.+
    import profunctor.P
    import profunctor.arrows.-->
    import profunctor.category.Obj

    def iterate[A: Obj, X: Obj](p: X --> (A + X)): (X --> A) = {
      conway.fix[A, X](p)
    }
  }

  /** The iteration of a trace *T* on coproducts: *p*† = *tr*(*p* ∘ *η*(∇)). */
  open class OfTraced(
    tracked val traced: Traced.On[StrongPromonad { val monoidal: Cocartesian }],
  ) extends Elgot(traced.strong) {
    import strong.{monoidal, profunctor}
    import monoidal.+
    import profunctor.{P, >>>}
    import profunctor.arrows.-->
    import profunctor.category.Obj

    private given TensorIsObj: [A: Obj, B: Obj] => ((A + B) is Obj) = monoidal.tensor.objects[A, B]

    def iterate[A: Obj, X: Obj](p: X --> (A + X)): (X --> A) = {
      traced.trace[X, A, X](profunctor.unit(monoidal.codiagonal[X]) >>> p)
    }
  }
}
