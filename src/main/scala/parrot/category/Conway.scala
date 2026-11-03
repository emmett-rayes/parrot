package parrot
package category

/** A parameterized fixed-point operator on a Freyd category over products.
  *
  * Represents a Conway operator, where
  *   - *p*†: *P*(*A*,*X*) for *p*: *P*(*A* × *X*,*X*) satisfies *p*† = ⟨*id*,*p*†⟩ ⨾ *p*: a solution of *x* =
  *     *p*(*a*,*x*)
  *
  * In a strict language this column of the grid is nearly empty: computing *p*† means running *p*†, so the least
  * solution is the nowhere-defined arrow, and useful recursion needs function types ([[Recursion]]) or guardedness.
  * Conway operators are equivalent to traces for products ([[Traced.OfConway]], [[Conway.OfTraced]]) and dual to
  * iteration: an Elgot operator is a Conway operator on the opposite category.
  */
abstract class Conway(tracked val strong: Strong.Bistrong.On[Promonad] { val monoidal: Cartesian })
    extends caps.Pure {
  import strong.{monoidal, profunctor}
  import monoidal.`*`
  import profunctor.{P, >>>}
  import profunctor.category.{Obj, -->}

  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = monoidal.tensor.objects[A, B]

  /** The fixed point *p*†: *P*(*A*,*X*) of *p*: *P*(*A* × *X*,*X*). */
  def fix[A: Obj, X: Obj](p: P[A * X, X]): P[A, X]

  /** Laws that any `Conway` operator must satisfy, with naturality and uniformity for pure arrows and dinaturality for
    * all arrows.
    */
  object ConwayLaws {

    /** *p*† = ⟨*id*,*p*†⟩ ⨾ *p*
      */
    def fixedPoint[A: Obj, X: Obj](p: P[A * X, X])(using P[A, X] is Observable): Boolean = {
      fix(p) =?= (profunctor.unit(monoidal.diagonal[A]) >>> strong.left[A, X, A](fix(p)) >>> p)
    }

    /** ((*h* × *id*) ⨾ *p*)† = *h* ⨾ *p*† for pure *h* */
    def parameterNaturality[A0: Obj, A1: Obj, X: Obj](p: P[A1 * X, X], h: A0 --> A1)(
      using P[A0, X] is Observable
    ): Boolean = {
      fix(strong.right[A0, A1, X](profunctor.unit(h)) >>> p) =?= (profunctor.unit(h) >>> fix(p))
    }

    /** (*f* ⨾ *g*)† = ((*id* × *g*) ⨾ *f*)† ⨾ *g* for pure *g* */
    def composition[A: Obj, X: Obj, Y: Obj](f: P[A * X, Y], g: Y --> X)(
      using P[A, X] is Observable
    ): Boolean = {
      fix[A, X](f >>> profunctor.unit(g)) =?=
        (fix[A, Y](strong.left[Y, X, A](profunctor.unit(g)) >>> f) >>> profunctor.unit(g))
    }

    /** (⟨*π*₁,*g*⟩ ⨾ *f*)† = ⟨*id*,(⟨*π*₁,*f*⟩ ⨾ *g*)†⟩ ⨾ *f* for *f*: *A* × *Y* → *X* and *g*: *A* × *X* → *Y*: a
      * fixed point of two arrows that feed each other can be taken through either.
      *
      * ⟨*π*₁,*g*⟩ keeps the parameter and runs *g*; with effects it is ⟨*π*₁,*id*⟩ ⨾ *τ*(*g*). [[composition]] is
      * the special case of a pure *g*.
      */
    def dinaturality[A: Obj, X: Obj, Y: Obj](f: P[A * Y, X], g: P[A * X, Y])(
      using P[A, X] is Observable
    ): Boolean = {
      val keepG = profunctor.unit(monoidal.pair(monoidal.fst[A, X], profunctor.category.identity[A * X])) >>>
        strong.left[A * X, Y, A](g)
      val keepF = profunctor.unit(monoidal.pair(monoidal.fst[A, Y], profunctor.category.identity[A * Y])) >>>
        strong.left[A * Y, X, A](f)
      fix[A, X](keepG >>> f) =?=
        (profunctor.unit(monoidal.diagonal[A]) >>> strong.left[A, Y, A](fix[A, Y](keepF >>> g)) >>> f)
    }

    /** (*p*†)† = (⟨*id*,*π*₂⟩ ⨾ *p*)† */
    def doubleDagger[A: Obj, X: Obj](p: P[(A * X) * X, X])(
      using P[A, X] is Observable
    ): Boolean = {
      fix[A, X](fix[A * X, X](p)) =?=
        fix[A, X](profunctor.unit(monoidal.pair(profunctor.category.identity[A * X], monoidal.snd[A, X])) >>> p)
    }

    /** If (*id* × *h*) ⨾ *g* = *f* ⨾ *h* for pure *h*, then *f*† ⨾ *h* = *g*†.
      *
      * @note The premise is not checked: *g* must be built to satisfy it.
      */
    def uniformity[A: Obj, X: Obj, Y: Obj](
      f: P[A * X, X],
      g: P[A * Y, Y],
      h: X --> Y,
    )(using P[A, Y] is Observable): Boolean = {
      (fix(f) >>> profunctor.unit(h)) =?= fix(g)
    }

    /** If *p* = *p*′, then *p*† = *p*′†.
      *
      * @note The premise is not checked: *p*′ must be equal to *p* by construction.
      */
    def congruence[A: Obj, X: Obj](p: P[A * X, X], p2: P[A * X, X])(
      using P[A, X] is Observable
    ): Boolean = {
      fix(p) =?= fix(p2)
    }
  }
}

object Conway {

  /** The parameterized fixed-point operators on a Freyd category with the strength *S*. */
  type On[S <: Strong.Bistrong] = Conway { val strong: S }

  /** Iteration read backwards: an Elgot operator on *P* is a Conway operator on *P*ᵒᵖ, whose products are the
    * coproducts of **C**. A step *P*(*X*,*A* + *X*) is an arrow *P*ᵒᵖ(*A* × *X*,*X*), and its iteration *P*(*X*,*A*) is
    * the fixed point *P*ᵒᵖ(*A*,*X*).
    */
  open class OfElgot(tracked val elgot: Elgot)
      extends Conway(Strong.Bistrong.Op(elgot.strong, elgot.strong.monoidal.op)) {
    import strong.{monoidal, profunctor}
    import monoidal.`*`
    import profunctor.P
    import profunctor.category.Obj

    def fix[A: Obj, X: Obj](p: P[A * X, X]): P[A, X] = {
      elgot.iterate[A, X](p)
    }
  }

  /** The fixed point of a trace on products: *p*† = *tr*(*p* ⨾ Δ). */
  open class OfTraced(
    tracked val traced: Traced.On[Strong.Bistrong.On[Promonad] { val monoidal: Cartesian }],
  ) extends Conway(traced.strong) {
    import strong.{monoidal, profunctor}
    import monoidal.`*`
    import profunctor.{P, >>>}
    import profunctor.category.Obj

    private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = monoidal.tensor.objects[A, B]

    def fix[A: Obj, X: Obj](p: P[A * X, X]): P[A, X] = {
      traced.trace[A, X, X](p >>> profunctor.unit(monoidal.diagonal[X]))
    }
  }
}
