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
abstract class Elgot(tracked val strong: Strong.Bistrong { val profunctor: Promonad; val monoidal: Cocartesian })
    extends caps.Pure {
  import strong.{monoidal, profunctor}
  import monoidal.+
  import profunctor.{P, >>>}
  import profunctor.category.{Obj, -->}

  private given TensorIsObj: [A: Obj, B: Obj] => ((A + B) is Obj) = monoidal.tensor.objects[A, B]

  /** The iteration *p*†: *P*(*X*,*A*) of *p*: *P*(*X*,*A* + *X*). */
  def iterate[A: Obj, X: Obj](p: P[X, A + X]): P[X, A]

  /** Laws that any `Elgot` operator must satisfy: the Conway iteration laws, with naturality and uniformity for pure
    * arrows and dinaturality for all arrows.
    */
  object ElgotLaws {

    /** *p*† = *p* ⨾ [*id*,*p*†]
      */
    def fixedPoint[A: Obj, X: Obj](p: P[X, A + X])(using P[X, A] is Observable): Boolean = {
      iterate(p) =?= (p >>> strong.left[X, A, A](iterate(p)) >>> profunctor.unit(monoidal.codiagonal[A]))
    }

    /** (*p* ⨾ (*h* + *id*))† = *p*† ⨾ *h* for pure *h* */
    def parameterNaturality[A: Obj, B: Obj, X: Obj](p: P[X, A + X], h: A --> B)(
      using P[X, B] is Observable
    ): Boolean = {
      iterate(p >>> strong.right[A, B, X](profunctor.unit(h))) =?= (iterate(p) >>> profunctor.unit(h))
    }

    /** (*g* ⨾ *p*)† = *g* ⨾ (*p* ⨾ (*id* + *g*))† for pure *g* */
    def composition[A: Obj, X: Obj, Y: Obj](p: P[Y, A + X], g: X --> Y)(
      using P[X, A] is Observable
    ): Boolean = {
      iterate[A, X](profunctor.unit(g) >>> p) =?=
        (profunctor.unit(g) >>> iterate[A, Y](p >>> strong.left[X, Y, A](profunctor.unit(g))))
    }

    /** (*f* ⨾ [*ι*₁,*g*])† = *f* ⨾ [*id*,(*g* ⨾ [*ι*₁,*f*])†] for *f*: *X* → *A* + *Y* and *g*: *Y* → *A* + *X*: a loop
      * that alternates two steps can start with either.
      *
      * [*ι*₁,*g*] runs *g* on the right and passes *A* through; with effects it is *τ*(*g*) ⨾ [*ι*₁,*id*].
      * [[composition]] is the special case of a pure *g*.
      */
    def dinaturality[A: Obj, X: Obj, Y: Obj](f: P[X, A + Y], g: P[Y, A + X])(
      using P[X, A] is Observable
    ): Boolean = {
      val fg = f >>> strong.left[Y, A + X, A](g) >>>
        profunctor.unit(monoidal.copair(monoidal.inl[A, X], profunctor.category.identity[A + X]))
      val gf = g >>> strong.left[X, A + Y, A](f) >>>
        profunctor.unit(monoidal.copair(monoidal.inl[A, Y], profunctor.category.identity[A + Y]))
      iterate[A, X](fg) =?= (f >>> strong.left[Y, A, A](iterate[A, Y](gf)) >>> profunctor.unit(monoidal.codiagonal[A]))
    }

    /** (*p*†)† = (*p* ⨾ [*id*,*ι*₂])† */
    def doubleDagger[A: Obj, X: Obj](p: P[X, (A + X) + X])(
      using P[X, A] is Observable
    ): Boolean = {
      iterate[A, X](iterate[A + X, X](p)) =?=
        iterate[A, X](p >>> profunctor.unit(monoidal.copair(profunctor.category.identity[A + X], monoidal.inr[A, X])))
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
      iterate(f) =?= (profunctor.unit(h) >>> iterate(g))
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
  open class OfConway(tracked val conway: Conway)
      extends Elgot(Strong.Bistrong.Op(conway.strong, conway.strong.monoidal.op)) {
    import strong.{monoidal, profunctor}
    import monoidal.+
    import profunctor.P
    import profunctor.category.Obj

    def iterate[A: Obj, X: Obj](p: P[X, A + X]): P[X, A] = {
      conway.fix[A, X](p)
    }
  }

  /** The iteration of a trace on coproducts: *p*† = *tr*(∇ ⨾ *p*). */
  open class OfTraced(
    tracked val traced: Traced { val strong: Strong.Bistrong { val profunctor: Promonad; val monoidal: Cocartesian } },
  ) extends Elgot(traced.strong) {
    import strong.{monoidal, profunctor}
    import monoidal.+
    import profunctor.{P, >>>}
    import profunctor.category.Obj

    private given TensorIsObj: [A: Obj, B: Obj] => ((A + B) is Obj) = monoidal.tensor.objects[A, B]

    def iterate[A: Obj, X: Obj](p: P[X, A + X]): P[X, A] = {
      traced.trace[X, A, X](profunctor.unit(monoidal.codiagonal[X]) >>> p)
    }
  }
}
