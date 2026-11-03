package parrot
package category

/** A trace on a Freyd category: feedback of the *U* part of an arrow into itself.
  *
  * Represents a traced premonoidal category, where
  *   - *tr*: *P*(*A* ⊗ *U*,*B* ⊗ *U*) → *P*(*A*,*B*) feeds the *U* output back into the *U* input
  *
  * With ⊗ the coproduct, *tr*(*p*) runs *p* until it leaves through *B*: a loop. With ⊗ the product, *tr*(*p*) solves
  * the equation *u* = *p*(*a*,*u*)₂: a recursive definition. The laws are those of traced monoidal categories, with
  * dinaturality (sliding) and superposing restricted to pure arrows, which are central.
  */
abstract class Traced(tracked val strong: Strong.Bistrong.On[Promonad]) extends caps.Pure {
  import strong.{monoidal, profunctor}
  import monoidal.{I, `*`}
  import profunctor.{P, >>>}
  import profunctor.category.{Obj, -->}

  private given IIsObj: (I is Obj) = monoidal.unit.evidence

  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = monoidal.tensor.objects[A, B]

  /** The trace *tr*: *P*(*A* ⊗ *U*,*B* ⊗ *U*) → *P*(*A*,*B*). */
  def trace[A: Obj, B: Obj, U: Obj](p: P[A * U, B * U]): P[A, B]

  /** Laws that any `Traced` structure must satisfy. */
  object TracedLaws {

    /** *tr*(*τ*′(*f*) ⨾ *p* ⨾ *τ*′(*g*)) = *f* ⨾ *tr*(*p*) ⨾ *g*
      */
    def tightening[A0: Obj, A1: Obj, B1: Obj, B0: Obj, U: Obj](
      f: P[A0, A1],
      p: P[A1 * U, B1 * U],
      g: P[B1, B0],
    )(using P[A0, B0] is Observable): Boolean = {
      trace(strong.right[A0, A1, U](f) >>> p >>> strong.right[B1, B0, U](g)) =?= (f >>> trace(p) >>> g)
    }

    /** *tr*(*p* ⨾ (*id* ⊗ *h*)) = *tr*((*id* ⊗ *h*) ⨾ *p*) for pure *h*: *U* → *V*
      */
    def sliding[A: Obj, B: Obj, U: Obj, V: Obj](
      p: P[A * V, B * U],
      h: U --> V,
    )(using P[A, B] is Observable): Boolean = {
      trace[A, B, V](p >>> profunctor.unit(monoidal.parallel(profunctor.category.identity[B], h)))
        =?= trace[A, B, U](profunctor.unit(monoidal.parallel(profunctor.category.identity[A], h)) >>> p)
    }

    /** *tr*ᴵ(*p*) = *ρ*⁻¹ ⨾ *p* ⨾ *ρ*
      */
    def vanishingUnit[A: Obj, B: Obj](p: P[A * I, B * I])(
      using P[A, B] is Observable
    ): Boolean = {
      trace(p) =?= (profunctor.unit(monoidal.rightUnitor[A].from) >>> p >>> profunctor.unit(monoidal.rightUnitor[B].to))
    }

    /** *tr*ᵁ⊗ⱽ(*p*) = *tr*ᵁ(*tr*ⱽ(*α* ⨾ *p* ⨾ *α*⁻¹))
      */
    def vanishingTensor[A: Obj, B: Obj, U: Obj, V: Obj](p: P[A * (U * V), B * (U * V)])(
      using P[A, B] is Observable
    ): Boolean = {
      val inner = profunctor.unit(monoidal.associator[A, U, V].to) >>> p >>>
        profunctor.unit(monoidal.associator[B, U, V].from)
      trace[A, B, U * V](p) =?= trace[A, B, U](trace[A * U, B * U, V](inner))
    }

    /** *tr*(*α* ⨾ (*g* ⊗ *p*) ⨾ *α*⁻¹) = *g* ⊗ *tr*(*p*) for pure *g*
      */
    def superposing[A: Obj, B: Obj, C: Obj, D: Obj, U: Obj](
      g: C --> D,
      p: P[A * U, B * U],
    )(using P[C * A, D * B] is Observable): Boolean = {
      val lhs = profunctor.unit(monoidal.associator[C, A, U].to) >>> strong.right[C, D, A * U](profunctor.unit(g)) >>>
        strong.left[A * U, B * U, D](p) >>> profunctor.unit(monoidal.associator[D, B, U].from)
      trace[C * A, D * B, U](lhs) =?= (strong.right[C, D, A](profunctor.unit(g)) >>> strong.left[A, B, D](trace(p)))
    }

    /** *tr*(*σ*) = *id*
      */
    def yanking[U: Obj](using P[U, U] is Observable): Boolean = {
      trace[U, U, U](profunctor.unit(monoidal.braid[U, U])) =?= profunctor.identity[U]
    }

    /** If *p* = *p*′, then *tr*(*p*) = *tr*(*p*′).
      *
      * @note The premise is not checked: *p*′ must be equal to *p* by construction.
      */
    def congruence[A: Obj, B: Obj, U: Obj](p: P[A * U, B * U], p2: P[A * U, B * U])(
      using P[A, B] is Observable
    ): Boolean = {
      trace(p) =?= trace(p2)
    }
  }
}

object Traced {

  /** The traces on a Freyd category with the strength *S*. */
  type On[S <: Strong.Bistrong] = Traced { val strong: S }

  /** The trace of an iteration: *tr*(*p*) = *ι*₁ ⨾ (*p* ⨾ (*id* + *ι*₂))†, a loop that starts on the left. */
  open class OfElgot(tracked val elgot: Elgot) extends Traced(elgot.strong) {
    import strong.{monoidal, profunctor}
    import monoidal.+
    import profunctor.{P, >>>}
    import profunctor.category.Obj

    private given TensorIsObj: [A: Obj, B: Obj] => ((A + B) is Obj) = monoidal.tensor.objects[A, B]

    def trace[A: Obj, B: Obj, U: Obj](p: P[A + U, B + U]): P[A, B] = {
      val step = p >>> profunctor.unit(monoidal.parallel(profunctor.category.identity[B], monoidal.inr[A, U]))
      profunctor.unit(monoidal.inl[A, U]) >>> elgot.iterate[B, A + U](step)
    }
  }

  /** The trace of a parameterized fixed point: *tr*(*p*) = ((*id* × *π*₂) ⨾ *p*)† ⨾ *π*₁. */
  open class OfConway(tracked val conway: Conway) extends Traced(conway.strong) {
    import strong.{monoidal, profunctor}
    import monoidal.`*`
    import profunctor.{P, >>>}
    import profunctor.category.Obj

    private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = monoidal.tensor.objects[A, B]

    def trace[A: Obj, B: Obj, U: Obj](p: P[A * U, B * U]): P[A, B] = {
      val step = profunctor.unit(monoidal.parallel(profunctor.category.identity[A], monoidal.snd[B, U])) >>> p
      conway.fix[A, B * U](step) >>> profunctor.unit(monoidal.fst[B, U])
    }
  }
}
