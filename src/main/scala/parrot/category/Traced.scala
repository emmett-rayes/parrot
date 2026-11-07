package parrot
package category

/** A trace structure on a bistrong promonad *P* over a symmetric monoidal category **M**.
  *
  * Represents a trace (Benton–Hyland) on the Freyd category of *P*, where
  *   - *tr*: *P*(*A* ⊗ *U*,*B* ⊗ *U*) → *P*(*A*,*B*) feeds the *U* output back into the *U* input
  *
  * With ⊗ the coproduct, *tr*(*p*) runs *p* until it leaves through *B*, i.e. a loop. With ⊗ the product, *tr*(*p*)
  * solves the recursive equation *u* = *p*(*a*,*u*)₂, i.e. a fixed point.
  *
  * Usually, a trace structure is defined on symmetric premonoidal categories. Here, we use a bistrong promonad over a
  * symmetric monoidal category instead. This allows us to lift the symmetry of the underlying monoidal category to the
  * trace structure.
  */
abstract class Traced(tracked val strong: StrongPromonad) extends caps.Pure {
  import strong.{monoidal, profunctor}
  import monoidal.{I, `*`, ***}
  import profunctor.{P, >>>}
  import profunctor.arrows.-->
  import profunctor.category.{Obj, identity, --> as ==>}

  /** The trace *tr*: *P*(*A* ⊗ *U*,*B* ⊗ *U*) → *P*(*A*,*B*) of *p*,
    *
    * The trace feeds its *U* output back into its *U* input.
    */
  def trace[A: Obj, B: Obj, U: Obj](p: (A * U) --> (B * U)): (A --> B)

  /** Laws that any `Traced` structure must satisfy. */
  object TracedLaws {
    private given IIsObj: (I is Obj)                                = monoidal.unit.evidence
    private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = monoidal.tensor.objects[A, B]

    /** *tr*(*τ*′(*g*) ∘ *p* ∘ *τ*′(*f*)) = *g* ∘ *tr*(*p*) ∘ *f*
      *
      * What happens before and after the loop can be moved out of it.
      *
      * @note The strength is used in place of the whiskering in the underlying premonoidal category.
      */
    def tightening[A0: Obj, A1: Obj, B1: Obj, B0: Obj, U: Obj](
      f: A0 --> A1,
      p: (A1 * U) --> (B1 * U),
      g: B1 --> B0,
    )(using (A0 --> B0) is Observable): Boolean = {
      trace(strong.right[A0, A1, U](f) >>> p >>> strong.right[B1, B0, U](g)) =?= (f >>> trace(p) >>> g)
    }

    /** *tr*ⱽ(*η*(*id* ⊗ *h*) ∘ *p*) = *tr*ᵁ(*p* ∘ *η*(*id* ⊗ *h*)) for pure *h*: *U* → *V*
      *
      * A pure map on the feedback wire can slide around the loop.
      */
    def sliding[A: Obj, B: Obj, U: Obj, V: Obj](
      p: (A * V) --> (B * U),
      h: U ==> V,
    )(using (A --> B) is Observable): Boolean = {
      trace[A, B, V](p >>> profunctor.unit(identity[B] *** h))
        =?= trace[A, B, U](profunctor.unit(identity[A] *** h) >>> p)
    }

    /** *tr*ᴵ(*p*) = *η*(*ρ*) ∘ *p* ∘ *η*(*ρ*⁻¹)
      *
      * Tracing out the unit does nothing.
      */
    def vanishingUnit[A: Obj, B: Obj](p: (A * I) --> (B * I))(
      using (A --> B) is Observable
    ): Boolean = {
      trace(p) =?= (profunctor.unit(monoidal.rightUnitor[A].from) >>> p >>> profunctor.unit(monoidal.rightUnitor[B].to))
    }

    /** *tr*ᵁ⊗ⱽ(*p*) = *tr*ᵁ(*tr*ⱽ(*η*(*α*⁻¹) ∘ *p* ∘ *η*(*α*)))
      *
      * Tracing out *U* ⊗ *V* is tracing out *V*, then *U*.
      */
    def vanishingTensor[A: Obj, B: Obj, U: Obj, V: Obj](p: (A * (U * V)) --> (B * (U * V)))(
      using (A --> B) is Observable
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
      g: C ==> D,
      p: (A * U) --> (B * U),
    )(using (C * A --> D * B) is Observable): Boolean = {
      val lhs = profunctor.unit(monoidal.associator[C, A, U].to) >>> strong.right[C, D, A * U](profunctor.unit(g)) >>>
        strong.left[A * U, B * U, D](p) >>> profunctor.unit(monoidal.associator[D, B, U].from)
      trace[C * A, D * B, U](lhs) =?= (strong.right[C, D, A](profunctor.unit(g)) >>> strong.left[A, B, D](trace(p)))
    }

    /** *tr*(*η*(*σ*)) = *id*
      *
      * Feeding one strand of a braid back into the other gives a straight wire.
      */
    def yanking[U: Obj](using (U --> U) is Observable): Boolean = {
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
    def centrality[A: Obj, B: Obj, C: Obj, D: Obj, U: Obj](f: (A * U) ==> (B * U), q: C --> D)(
      using (A * C --> B * D) is Observable
    ): Boolean = {
      val c = trace[A, B, U](profunctor.unit(f))
      (strong.right[A, B, C](c) >>> strong.left[C, D, B](q)) =?= (strong.left[C, D, A](q) >>> strong.right[A, B, D](c))
    }

    /** If *p* = *p*′, then *tr*(*p*) = *tr*(*p*′).
      *
      * @note The premise is not checked: *p*′ must be equal to *p* by construction.
      */
    def congruence[A: Obj, B: Obj, U: Obj](p: (A * U) --> (B * U), p2: (A * U) --> (B * U))(
      using (A --> B) is Observable
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
    import monoidal.{+, +++}
    import profunctor.{P, >>>}
    import profunctor.arrows.-->
    import profunctor.category.{Obj, identity}

    private given TensorIsObj: [A: Obj, B: Obj] => ((A + B) is Obj) = monoidal.tensor.objects[A, B]

    def trace[A: Obj, B: Obj, U: Obj](p: (A + U) --> (B + U)): (A --> B) = {
      val step = p >>> profunctor.unit(identity[B] +++ monoidal.inr[A, U])
      profunctor.unit(monoidal.inl[A, U]) >>> elgot.iterate[B, A + U](step)
    }
  }

  /** The trace of a parameterized fixed point *C*: *tr*(*p*) = *η*(*π*₁) ∘ (*p* ∘ *η*(*id* × *π*₂))†. */
  open class OfConway(tracked val conway: Conway) extends Traced(conway.strong) {
    import strong.{monoidal, profunctor}
    import monoidal.{`*`, ***}
    import profunctor.{P, >>>}
    import profunctor.arrows.-->
    import profunctor.category.{Obj, identity}

    private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = monoidal.tensor.objects[A, B]

    def trace[A: Obj, B: Obj, U: Obj](p: (A * U) --> (B * U)): (A --> B) = {
      val step = profunctor.unit(identity[A] *** monoidal.snd[B, U]) >>> p
      conway.fix[A, B * U](step) >>> profunctor.unit(monoidal.fst[B, U])
    }
  }
}
