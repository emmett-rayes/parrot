package parrot
package category

/** A trace structure on a symmetric premonoidal category **C**.
  *
  * Represents a trace (Benton–Hyland), where
  *   - *tr*: **C**(*A* ⊗ *U*,*B* ⊗ *U*) → **C**(*A*,*B*) feeds the *U* output back into the *U* input
  *
  * The notion is a trace on a centred symmetric premonoidal category *J*: **M** → **C**, with a chosen category **M**
  * of pure morphisms, which are central, i.e. they interchange with every morphism. The structure is on **C**, and
  * the law that speaks of pure morphisms, sliding, takes *J* as an argument. In a monoidal category, *J* is the
  * identity functor. In a Freyd category, it is the functor of the pure arrows *η*(*f*) of its base.
  *
  * @note The axiom of centre preservation, that the trace of a pure morphism is pure, says that a morphism is in the
  *   image of *J*, which a law that returns a `Boolean` cannot state. The laws check its consequence instead: the
  *   trace of a central morphism is central ([[TracedLaws.Consequences.centrality]]).
  */
abstract class Traced(tracked val premonoidal: Premonoidal & SymmetricPremonoidal) extends caps.Pure {
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

    /** *tr*ⱽ((*B* ⊘ *J*(*h*)) ∘ *p*) = *tr*ᵁ(*p* ∘ (*A* ⊘ *J*(*h*))) for *h*: *U* → *V* in **M**
      *
      * A pure map on the feedback wire can slide around the loop. The functor *J*: **M** → **C** picks out the pure
      * morphisms, such as [[Promonad.pure]] of a Freyd category.
      *
      * @note Not every functor into **C** will do: the law is for the functors into the centre. Being central is not
      *   enough for the morphism that slides.
      */
    def sliding(centre: Functor.Into[premonoidal.category.type])[
      A: Obj,
      B: Obj,
      U: centre.source.Obj,
      V: centre.source.Obj,
    ](
      p: (A * centre.F[V]) --> (B * centre.F[U]),
      h: centre.source.Hom[U, V],
    )(using (A --> B) is Observable): Boolean = {
      given JUIsObj: (centre.F[U] is Obj) = centre.objects[U]
      given JVIsObj: (centre.F[V] is Obj) = centre.objects[V]
      val pure                            = centre.map(h)
      trace[A, B, centre.F[V]](p >>> rmap[centre.F[U], centre.F[V], B](pure)) =?=
        trace[A, B, centre.F[U]](rmap[centre.F[U], centre.F[V], A](pure) >>> p)
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

    /** *tr*(*α*⁻¹ ∘ (*D* ⊘ *p*) ∘ (*g* ⦸ (*A* ⊗ *U*)) ∘ *α*) = (*D* ⊘ *tr*(*p*)) ∘ (*g* ⦸ *A*)
      *
      * A wire that does not take part in the loop can be drawn beside it, and so can what happens on that wire before
      * the loop.
      *
      * @note The law holds for every *g*: *C* → *D*, since *g* runs before the loop. The naturality of the associator
      *   in its first component moves *g* out of the associator, [[tightening]] moves it out of the trace, and what
      *   remains is the case *g* = *id*, which is the axiom of Benton and Hyland.
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

    /** If *p* = *p*′, then *tr*(*p*) = *tr*(*p*′).
      *
      * @note The premise is not checked: *p*′ must be equal to *p* by construction.
      */
    def congruence[A: Obj, B: Obj, U: Obj](p: (A * U) --> (B * U), p2: (A * U) --> (B * U))(
      using (A --> B) is Observable
    ): Boolean = {
      trace(p) =?= trace(p2)
    }

    /** Laws that follow from the others: theorems, checked as tests. */
    object Consequences {

      /** (*B* ⊘ *q*) ∘ (*tr*(*f*) ⦸ *C*) = (*tr*(*f*) ⦸ *D*) ∘ (*A* ⊘ *q*)
        *
        * The trace of a central morphism is central: it interchanges with every morphism *q*. This is Proposition 3.3
        * of Benton and Hyland, a consequence of the other laws.
        *
        * @note Holds for a central *f*, such as a pure arrow of a Freyd category. The premise is not checked. The law
        *   states that *c* = *tr*(*f*) interchanges with *q* on its right. On its left it follows by the naturality of
        *   the braiding in each component: *C* ⊘ *c* = *σ* ∘ (*c* ⦸ *C*) ∘ *σ*.
        */
      def centrality[A: Obj, B: Obj, C: Obj, D: Obj, U: Obj](f: (A * U) --> (B * U), q: C --> D)(
        using (A * C --> B * D) is Observable
      ): Boolean = {
        val c = trace[A, B, U](f)
        (lmap[A, B, C](c) >>> rmap[C, D, B](q)) =?= (rmap[C, D, A](q) >>> lmap[A, B, D](c))
      }
    }
  }
}

object Traced {

  /** The trace structures on a symmetric premonoidal category **C**. */
  type On[C <: Premonoidal & SymmetricPremonoidal] = Traced { val premonoidal: C }

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
