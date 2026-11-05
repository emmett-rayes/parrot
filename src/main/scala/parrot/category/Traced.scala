package parrot
package category

/** A trace structure on a bistrong promonad *P* over a symmetric monoidal category **M**.
  *
  * Represents a trace (Benton–Hyland) on the Freyd category of *P*, where
  *   - *tr*: *P*(*A* ⊗ *U*,*B* ⊗ *U*) → *P*(*A*,*B*) feeds the *U* output back into the *U* input
  *
  * With ⊗ the coproduct, *tr*(*p*) runs *p* until it leaves through *B*: a loop. With ⊗ the product, *tr*(*p*) solves
  * the equation *u* = *p*(*a*,*u*)₂: a recursive definition. The laws are those of traced monoidal categories, with
  * sliding and superposing restricted to pure arrows, which are central.
  */
abstract class Traced(tracked val strong: StrongPromonad) extends caps.Pure {
  import strong.{monoidal, profunctor}
  import monoidal.{I, `*`}
  import profunctor.{P, >>>}
  import profunctor.category.{Obj, -->}

  /** The trace *tr*: *P*(*A* ⊗ *U*,*B* ⊗ *U*) → *P*(*A*,*B*) of *p*, which feeds its *U* output back into its *U*
    * input.
    */
  def trace[A: Obj, B: Obj, U: Obj](p: P[A * U, B * U]): P[A, B]

  private given IIsObj: (I is Obj)                                = monoidal.unit.evidence
  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = monoidal.tensor.objects[A, B]

  /** Laws that any `Traced` structure must satisfy.
    *
    * The trace is natural in *A* and *B*, dinatural in *U* for pure arrows, vanishing, superposing for pure arrows,
    * yanking and central on pure arrows.
    */
  object TracedLaws {

    /** *tr*(*τ*′(*g*) ∘ *p* ∘ *τ*′(*f*)) = *g* ∘ *tr*(*p*) ∘ *f*
      *
      * What happens before and after the loop can be moved out of it.
      */
    def tightening[A0: Obj, A1: Obj, B1: Obj, B0: Obj, U: Obj](
      f: P[A0, A1],
      p: P[A1 * U, B1 * U],
      g: P[B1, B0],
    )(using P[A0, B0] is Observable): Boolean = {
      trace(strong.right[A0, A1, U](f) >>> p >>> strong.right[B1, B0, U](g)) =?= (f >>> trace(p) >>> g)
    }

    /** *tr*ⱽ(*η*(*id* ⊗ *h*) ∘ *p*) = *tr*ᵁ(*p* ∘ *η*(*id* ⊗ *h*)) for pure *h*: *U* → *V*
      *
      * A pure map on the feedback wire can slide around the loop.
      */
    def sliding[A: Obj, B: Obj, U: Obj, V: Obj](
      p: P[A * V, B * U],
      h: U --> V,
    )(using P[A, B] is Observable): Boolean = {
      trace[A, B, V](p >>> profunctor.unit(monoidal.parallel(profunctor.category.identity[B], h)))
        =?= trace[A, B, U](profunctor.unit(monoidal.parallel(profunctor.category.identity[A], h)) >>> p)
    }

    /** *tr*ᴵ(*p*) = *η*(*ρ*) ∘ *p* ∘ *η*(*ρ*⁻¹)
      *
      * Tracing out the unit does nothing.
      */
    def vanishingUnit[A: Obj, B: Obj](p: P[A * I, B * I])(
      using P[A, B] is Observable
    ): Boolean = {
      trace(p) =?= (profunctor.unit(monoidal.rightUnitor[A].from) >>> p >>> profunctor.unit(monoidal.rightUnitor[B].to))
    }

    /** *tr*ᵁ⊗ⱽ(*p*) = *tr*ᵁ(*tr*ⱽ(*η*(*α*⁻¹) ∘ *p* ∘ *η*(*α*)))
      *
      * Tracing out *U* ⊗ *V* is tracing out *V*, then *U*.
      */
    def vanishingTensor[A: Obj, B: Obj, U: Obj, V: Obj](p: P[A * (U * V), B * (U * V)])(
      using P[A, B] is Observable
    ): Boolean = {
      val inner = profunctor.unit(monoidal.associator[A, U, V].to) >>> p >>>
        profunctor.unit(monoidal.associator[B, U, V].from)
      trace[A, B, U * V](p) =?= trace[A, B, U](trace[A * U, B * U, V](inner))
    }

    /** *tr*(*η*(*α*⁻¹) ∘ (*η*(*g*) ⋉ *p*) ∘ *η*(*α*)) = *η*(*g*) ⋉ *tr*(*p*) for pure *g*
      *
      * A wire that does not take part in the loop can be drawn beside it.
      */
    def superposing[A: Obj, B: Obj, C: Obj, D: Obj, U: Obj](
      g: C --> D,
      p: P[A * U, B * U],
    )(using P[C * A, D * B] is Observable): Boolean = {
      val lhs = profunctor.unit(monoidal.associator[C, A, U].to) >>> strong.right[C, D, A * U](profunctor.unit(g)) >>>
        strong.left[A * U, B * U, D](p) >>> profunctor.unit(monoidal.associator[D, B, U].from)
      trace[C * A, D * B, U](lhs) =?= (strong.right[C, D, A](profunctor.unit(g)) >>> strong.left[A, B, D](trace(p)))
    }

    /** *tr*(*η*(*σ*)) = *id*
      *
      * Feeding one strand of a braid back into the other gives a straight wire.
      */
    def yanking[U: Obj](using P[U, U] is Observable): Boolean = {
      trace[U, U, U](profunctor.unit(monoidal.braid[U, U])) =?= profunctor.identity[U]
    }

    /** *τ*(*q*) ∘ *τ*′(*tr*(*η*(*f*))) = *τ*′(*tr*(*η*(*f*))) ∘ *τ*(*q*) for pure *f*
      *
      * The trace of a pure arrow is central: it interchanges with every arrow *q*.
      *
      * @note The law states that *c* = *tr*(*η*(*f*)) interchanges with *q* on its right. On its left it follows by the
      *   braiding law of the strength, *τ*′ = *P*(*σ*,*σ*) ∘ *τ*: *τ*′(*q*) ∘ *τ*(*c*) = *η*(*σ*) ∘ *τ*(*q*) ∘
      *   *τ*′(*c*) ∘ *η*(*σ*) and *τ*(*c*) ∘ *τ*′(*q*) = *η*(*σ*) ∘ *τ*′(*c*) ∘ *τ*(*q*) ∘ *η*(*σ*).
      */
    def centrality[A: Obj, B: Obj, C: Obj, D: Obj, U: Obj](f: (A * U) --> (B * U), q: P[C, D])(
      using P[A * C, B * D] is Observable
    ): Boolean = {
      val c = trace[A, B, U](profunctor.unit(f))
      (strong.right[A, B, C](c) >>> strong.left[C, D, B](q)) =?= (strong.left[C, D, A](q) >>> strong.right[A, B, D](c))
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

  /** The trace structures on a bistrong promonad with the strength *S*. */
  type On[S <: Bistrong] = Traced { val strong: S }

  /** The trace of an iteration *E*: *tr*(*p*) = (*η*(*id* + *ι*₂) ∘ *p*)† ∘ *η*(*ι*₁), a loop that starts on the left.
    */
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

  /** The trace of a parameterized fixed point *C*: *tr*(*p*) = *η*(*π*₁) ∘ (*p* ∘ *η*(*id* × *π*₂))†. */
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
