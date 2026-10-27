package parrot
package category

/** An iteration operator on a Freyd category over coproducts.
  *
  * Represents an Elgot operator, where
  *   - *p*†: *P*(*X*,*A*) for *p*: *P*(*X*,*A* + *X*) satisfies *p*† = *p* ⨾ [*id*,*p*†]: run *p*; on *A* stop, on *X*
  *     run again
  *
  * In 𝒫 this is the while loop, defined for every *p*. In 𝒮 it cannot be: deciding whether a loop stops is the
  * halting problem. Total instances are guarded: they stop with failure on a step that makes no progress, and satisfy
  * the laws for the steps that always make progress. Elgot operators are equivalent to traces for coproducts
  * ([[Traced.OfElgot]], [[Elgot.OfTraced]]).
  */
abstract class Elgot(tracked val S: Strong { val P: Promonad; val M: Cocartesian }) extends caps.Pure {
  import S.M.{+, given}
  import S.P.{P, >>}
  import S.P.K.{Obj, -->}

  /** The iteration *p*†: *P*(*X*,*A*) of *p*: *P*(*X*,*A* + *X*). */
  def iterate[A: Obj, X: Obj](p: P[X, A + X]): P[X, A]

  /** Laws that any `Elgot` operator must satisfy: the Conway iteration laws, with naturality and uniformity for pure
    * arrows and dinaturality for all arrows.
    */
  object ElgotLaws {

    /** *p*† = *p* ⨾ [*id*,*p*†]
      */
    def fixedPoint[A: Obj, X: Obj](p: P[X, A + X])(using P[X, A] is Observable): Boolean = {
      iterate(p) =?= (p >> S.second[X, A, A](iterate(p)) >> S.P.unit(S.M.codiagonal[A]))
    }

    /** (*p* ⨾ (*h* + *id*))† = *p*† ⨾ *h* for pure *h* */
    def parameterNaturality[A: Obj, B: Obj, X: Obj](p: P[X, A + X], h: A --> B)(
      using P[X, B] is Observable
    ): Boolean = {
      iterate(p >> S.first[A, B, X](S.P.unit(h))) =?= (iterate(p) >> S.P.unit(h))
    }

    /** (*g* ⨾ *p*)† = *g* ⨾ (*p* ⨾ (*id* + *g*))† for pure *g* */
    def composition[A: Obj, X: Obj, Y: Obj](p: P[Y, A + X], g: X --> Y)(
      using P[X, A] is Observable
    ): Boolean = {
      iterate[A, X](S.P.unit(g) >> p) =?= (S.P.unit(g) >> iterate[A, Y](p >> S.second[X, Y, A](S.P.unit(g))))
    }

    /** (*f* ⨾ [*ι*₁,*g*])† = *f* ⨾ [*id*,(*g* ⨾ [*ι*₁,*f*])†] for *f*: *X* → *A* + *Y* and *g*: *Y* → *A* + *X*: a loop
      * that alternates two steps can start with either.
      *
      * [*ι*₁,*g*] runs *g* on the right and passes *A* through; with effects it is *second*(*g*) ⨾ [*ι*₁,*id*].
      * [[composition]] is the special case of a pure *g*.
      */
    def dinaturality[A: Obj, X: Obj, Y: Obj](f: P[X, A + Y], g: P[Y, A + X])(
      using P[X, A] is Observable
    ): Boolean = {
      val fg = f >> S.second[Y, A + X, A](g) >> S.P.unit(S.M.copair(S.M.inl[A, X], S.P.K.identity[A + X]))
      val gf = g >> S.second[X, A + Y, A](f) >> S.P.unit(S.M.copair(S.M.inl[A, Y], S.P.K.identity[A + Y]))
      iterate[A, X](fg) =?= (f >> S.second[Y, A, A](iterate[A, Y](gf)) >> S.P.unit(S.M.codiagonal[A]))
    }

    /** (*p*†)† = (*p* ⨾ [*id*,*ι*₂])† */
    def doubleDagger[A: Obj, X: Obj](p: P[X, (A + X) + X])(
      using P[X, A] is Observable
    ): Boolean = {
      iterate[A, X](iterate[A + X, X](p)) =?=
        iterate[A, X](p >> S.P.unit(S.M.copair(S.P.K.identity[A + X], S.M.inr[A, X])))
    }

    /** If *f* ⨾ (*id* + *h*) = *h* ⨾ *g* for pure *h*, then *f*† = *h* ⨾ *g*†.
      *
      * @note The premise is not checked: *g* must be built to satisfy it.
      */
    def uniformity[A: Obj, X: Obj, Y: Obj](
      f: P[X, A + X],
      g: P[Y, A + Y],
      h: X --> Y,
    )(using P[X, A] is Observable): Boolean = {
      iterate(f) =?= (S.P.unit(h) >> iterate(g))
    }

    /** If *p* = *p*′, then *p*† = *p*′†.
      *
      * @note The premise is not checked: *p*′ must be equal to *p* by construction.
      */
    def congruence[A: Obj, X: Obj](p: P[X, A + X], p2: P[X, A + X])(
      using P[X, A] is Observable
    ): Boolean = {
      iterate(p) =?= iterate(p2)
    }
  }
}

object Elgot {

  /** Fixed points read backwards: a Conway operator on *P* is an Elgot operator on *P*ᵒᵖ. */
  open class OfConway(tracked val C: Conway) extends Elgot(Strong.OpOfProduct(C.S)) {
    import S.M.+
    import S.P.P
    import S.P.K.Obj

    def iterate[A: Obj, X: Obj](p: P[X, A + X]): P[X, A] = {
      C.fix[A, X](p)
    }
  }

  /** The iteration of a trace on coproducts: *p*† = *tr*(∇ ⨾ *p*). */
  open class OfTraced(tracked val T: Traced { val S: Strong { val P: Promonad; val M: Cocartesian } })
      extends Elgot(T.S) {
    import S.M.{+, given}
    import S.P.{P, >>}
    import S.P.K.Obj

    def iterate[A: Obj, X: Obj](p: P[X, A + X]): P[X, A] = {
      T.trace[X, A, X](S.P.unit(S.M.codiagonal[X]) >> p)
    }
  }
}
