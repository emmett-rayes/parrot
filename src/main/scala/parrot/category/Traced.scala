package parrot
package category

/** A trace structure on a symmetric premonoidal category **C**.
  *
  * Represents a trace (Benton–Hyland), where
  *   - *tr*: **C**(*A* ⊗ *U*,*B* ⊗ *U*) → **C**(*A*,*B*) feeds the *U* output back into the *U* input
  *
  * With ⊗ the coproduct, *tr*(*p*) runs *p* until it leaves through *B*, i.e. a loop. With ⊗ the product, *tr*(*p*)
  * solves the recursive equation *u* = *p*(*a*,*u*)₂, i.e. a fixed point.
  *
  * Sliding and superposing hold for central morphisms, which interchange with every morphism: in a monoidal category
  * these are all morphisms, in a Freyd category the pure arrows ([[Freyd]]).
  */
abstract class Traced(tracked val premonoidal: SymmetricPremonoidal) extends caps.Pure {
  import premonoidal.{I, `*`, associator, braid, lmap, rightUnitor, rmap}
  import premonoidal.category.{Obj, identity, -->, >>>}

  /** The trace *tr*: **C**(*A* ⊗ *U*,*B* ⊗ *U*) → **C**(*A*,*B*) of *p*.
    *
    * The trace feeds its *U* output back into its *U* input.
    */
  def trace[A: Obj, B: Obj, U: Obj](p: (A * U) --> (B * U)): (A --> B)

  /** Laws that any `Traced` structure must satisfy. */
  object TracedLaws {
    private given IIsObj: (I is Obj)                                = premonoidal.unit.evidence
    private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = premonoidal.tensor.objects[A, B]

    /** *tr*((*g* ⦸ *U*) ∘ *p* ∘ (*f* ⦸ *U*)) = *g* ∘ *tr*(*p*) ∘ *f*
      *
      * What happens before and after the loop can be moved out of it.
      */
    def tightening[A0: Obj, A1: Obj, B1: Obj, B0: Obj, U: Obj](
      f: A0 --> A1,
      p: (A1 * U) --> (B1 * U),
      g: B1 --> B0,
    )(using (A0 --> B0) is Observable): Boolean = {
      trace(lmap[A0, A1, U](f) >>> p >>> lmap[B1, B0, U](g)) =?= (f >>> trace(p) >>> g)
    }

    /** *tr*ⱽ((*B* ⊘ *h*) ∘ *p*) = *tr*ᵁ(*p* ∘ (*A* ⊘ *h*)) for central *h*: *U* → *V*
      *
      * A central map on the feedback wire can slide around the loop.
      *
      * @note The premise is not checked: *h* must be central, such as a pure arrow of a Freyd category.
      */
    def sliding[A: Obj, B: Obj, U: Obj, V: Obj](
      p: (A * V) --> (B * U),
      h: U --> V,
    )(using (A --> B) is Observable): Boolean = {
      trace[A, B, V](p >>> rmap[U, V, B](h)) =?= trace[A, B, U](rmap[U, V, A](h) >>> p)
    }

    /** *tr*ᴵ(*p*) = *ρ* ∘ *p* ∘ *ρ*⁻¹
      *
      * Tracing out the unit does nothing.
      */
    def vanishingUnit[A: Obj, B: Obj](p: (A * I) --> (B * I))(
      using (A --> B) is Observable
    ): Boolean = {
      trace(p) =?= (rightUnitor[A].from >>> p >>> rightUnitor[B].to)
    }

    /** *tr*ᵁ⊗ⱽ(*p*) = *tr*ᵁ(*tr*ⱽ(*α*⁻¹ ∘ *p* ∘ *α*))
      *
      * Tracing out *U* ⊗ *V* is tracing out *V*, then *U*.
      */
    def vanishingTensor[A: Obj, B: Obj, U: Obj, V: Obj](p: (A * (U * V)) --> (B * (U * V)))(
      using (A --> B) is Observable
    ): Boolean = {
      val inner = associator[A, U, V].to >>> p >>> associator[B, U, V].from
      trace[A, B, U * V](p) =?= trace[A, B, U](trace[A * U, B * U, V](inner))
    }

    /** *tr*(*α*⁻¹ ∘ (*D* ⊘ *p*) ∘ (*g* ⦸ (*A* ⊗ *U*)) ∘ *α*) = (*D* ⊘ *tr*(*p*)) ∘ (*g* ⦸ *A*) for central *g*
      *
      * A wire that does not take part in the loop can be drawn beside it.
      *
      * @note The premise is not checked: *g*: *C* → *D* must be central, such as a pure arrow of a Freyd category.
      */
    def superposing[A: Obj, B: Obj, C: Obj, D: Obj, U: Obj](
      g: C --> D,
      p: (A * U) --> (B * U),
    )(using (C * A --> D * B) is Observable): Boolean = {
      val lhs = associator[C, A, U].to >>> lmap[C, D, A * U](g) >>> rmap[A * U, B * U, D](p) >>>
        associator[D, B, U].from
      trace[C * A, D * B, U](lhs) =?= (lmap[C, D, A](g) >>> rmap[A, B, D](trace(p)))
    }

    /** *tr*(*σ*) = *id*
      *
      * Feeding one strand of a braid back into the other gives a straight wire.
      */
    def yanking[U: Obj](using (U --> U) is Observable): Boolean = {
      trace[U, U, U](braid[U, U]) =?= identity[U]
    }

    /** (*B* ⊘ *q*) ∘ (*tr*(*f*) ⦸ *C*) = (*tr*(*f*) ⦸ *D*) ∘ (*A* ⊘ *q*) for central *f*
      *
      * The trace of a central morphism is central: it interchanges with every morphism *q*.
      *
      * @note The premise is not checked: *f* must be central, such as a pure arrow of a Freyd category. The law states
      *   that *c* = *tr*(*f*) interchanges with *q* on its right. On its left it follows by the naturality of the
      *   braiding in each component: *C* ⊘ *c* = *σ* ∘ (*c* ⦸ *C*) ∘ *σ*.
      */
    def centrality[A: Obj, B: Obj, C: Obj, D: Obj, U: Obj](f: (A * U) --> (B * U), q: C --> D)(
      using (A * C --> B * D) is Observable
    ): Boolean = {
      val c = trace[A, B, U](f)
      (lmap[A, B, C](c) >>> rmap[C, D, B](q)) =?= (rmap[C, D, A](q) >>> lmap[A, B, D](c))
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

  /** The trace structures on a symmetric premonoidal category **C**. */
  type On[C <: SymmetricPremonoidal] = Traced { val premonoidal: C }

  /** The trace of an iteration *E*, on its Freyd category: *tr*(*p*) = (*η*(*id* + *ι*₂) ∘ *p*)† ∘ *η*(*ι*₁), a loop
    * that starts on the left.
    */
  open class OfElgot(tracked val elgot: Elgot) extends Traced(Freyd(elgot.strong)) {
    import premonoidal.strong.{monoidal, profunctor}
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

  /** The trace of a parameterized fixed point *C*, on its Freyd category: *tr*(*p*) = *η*(*π*₁) ∘ (*p* ∘ *η*(*id* ×
    * *π*₂))†.
    */
  open class OfConway(tracked val conway: Conway) extends Traced(Freyd(conway.strong)) {
    import premonoidal.strong.{monoidal, profunctor}
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
