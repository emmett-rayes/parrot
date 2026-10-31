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
abstract class Conway(tracked val S: Strong.Bistrong { val P: Promonad; val M: Cartesian }) extends caps.Pure {
  import S.M.{`*`, given}
  import S.P.{P, >>>}
  import S.P.K.{Obj, -->}

  /** The fixed point *p*†: *P*(*A*,*X*) of *p*: *P*(*A* × *X*,*X*). */
  def fix[A: Obj, X: Obj](p: P[A * X, X]): P[A, X]

  /** Laws that any `Conway` operator must satisfy, with naturality and uniformity for pure arrows and dinaturality for
    * all arrows.
    */
  object ConwayLaws {

    /** *p*† = ⟨*id*,*p*†⟩ ⨾ *p*
      */
    def fixedPoint[A: Obj, X: Obj](p: P[A * X, X])(using P[A, X] is Observable): Boolean = {
      fix(p) =?= (S.P.unit(S.M.diagonal[A]) >>> S.left[A, X, A](fix(p)) >>> p)
    }

    /** ((*h* × *id*) ⨾ *p*)† = *h* ⨾ *p*† for pure *h* */
    def parameterNaturality[A0: Obj, A1: Obj, X: Obj](p: P[A1 * X, X], h: A0 --> A1)(
      using P[A0, X] is Observable
    ): Boolean = {
      fix(S.right[A0, A1, X](S.P.unit(h)) >>> p) =?= (S.P.unit(h) >>> fix(p))
    }

    /** (*f* ⨾ *g*)† = ((*id* × *g*) ⨾ *f*)† ⨾ *g* for pure *g* */
    def composition[A: Obj, X: Obj, Y: Obj](f: P[A * X, Y], g: Y --> X)(
      using P[A, X] is Observable
    ): Boolean = {
      fix[A, X](f >>> S.P.unit(g)) =?= (fix[A, Y](S.left[Y, X, A](S.P.unit(g)) >>> f) >>> S.P.unit(g))
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
      val keepG = S.P.unit(S.M.pair(S.M.fst[A, X], S.P.K.identity[A * X])) >>> S.left[A * X, Y, A](g)
      val keepF = S.P.unit(S.M.pair(S.M.fst[A, Y], S.P.K.identity[A * Y])) >>> S.left[A * Y, X, A](f)
      fix[A, X](keepG >>> f) =?= (S.P.unit(S.M.diagonal[A]) >>> S.left[A, Y, A](fix[A, Y](keepF >>> g)) >>> f)
    }

    /** (*p*†)† = (⟨*id*,*π*₂⟩ ⨾ *p*)† */
    def doubleDagger[A: Obj, X: Obj](p: P[(A * X) * X, X])(
      using P[A, X] is Observable
    ): Boolean = {
      fix[A, X](fix[A * X, X](p)) =?= fix[A, X](S.P.unit(S.M.pair(S.P.K.identity[A * X], S.M.snd[A, X])) >>> p)
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
      (fix(f) >>> S.P.unit(h)) =?= fix(g)
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

  /** Iteration read backwards: an Elgot operator on *P* is a Conway operator on *P*ᵒᵖ, whose products are the
    * coproducts of **K**. A step *P*(*X*,*A* + *X*) is an arrow *P*ᵒᵖ(*A* × *X*,*X*), and its iteration *P*(*X*,*A*) is
    * the fixed point *P*ᵒᵖ(*A*,*X*).
    */
  open class OfElgot(tracked val E: Elgot) extends Conway(Strong.Bistrong.Op(E.S, E.S.M.op)) {
    import S.M.`*`
    import S.P.P
    import S.P.K.Obj

    def fix[A: Obj, X: Obj](p: P[A * X, X]): P[A, X] = {
      E.iterate[A, X](p)
    }
  }

  /** The fixed point of a trace on products: *p*† = *tr*(*p* ⨾ Δ). */
  open class OfTraced(tracked val T: Traced { val S: Strong.Bistrong { val P: Promonad; val M: Cartesian } })
      extends Conway(T.S) {
    import S.M.{`*`, given}
    import S.P.{P, >>>}
    import S.P.K.Obj

    def fix[A: Obj, X: Obj](p: P[A * X, X]): P[A, X] = {
      T.trace[A, X, X](p >>> S.P.unit(S.M.diagonal[X]))
    }
  }
}
