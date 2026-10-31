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
abstract class Traced(tracked val S: Strong.Bistrong { val P: Promonad }) extends caps.Pure {
  import S.M.{I, `*`, given}
  import S.P.{P, >>}
  import S.P.K.{Obj, -->}

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
      trace(S.right[A0, A1, U](f) >> p >> S.right[B1, B0, U](g)) =?= (f >> trace(p) >> g)
    }

    /** *tr*(*p* ⨾ (*id* ⊗ *h*)) = *tr*((*id* ⊗ *h*) ⨾ *p*) for pure *h*: *U* → *V*
      */
    def sliding[A: Obj, B: Obj, U: Obj, V: Obj](
      p: P[A * V, B * U],
      h: U --> V,
    )(using P[A, B] is Observable): Boolean = {
      trace[A, B, V](p >> S.P.unit(S.M.tensor(S.P.K.identity[B], h))) =?=
        trace[A, B, U](S.P.unit(S.M.tensor(S.P.K.identity[A], h)) >> p)
    }

    /** *tr*ᴵ(*p*) = *ρ*⁻¹ ⨾ *p* ⨾ *ρ*
      */
    def vanishingUnit[A: Obj, B: Obj](p: P[A * I, B * I])(
      using P[A, B] is Observable
    ): Boolean = {
      trace(p) =?= (S.P.unit(S.M.rightUnitor[A].from) >> p >> S.P.unit(S.M.rightUnitor[B].to))
    }

    /** *tr*ᵁ⊗ⱽ(*p*) = *tr*ᵁ(*tr*ⱽ(*α* ⨾ *p* ⨾ *α*⁻¹))
      */
    def vanishingTensor[A: Obj, B: Obj, U: Obj, V: Obj](p: P[A * (U * V), B * (U * V)])(
      using P[A, B] is Observable
    ): Boolean = {
      val inner = S.P.unit(S.M.associator[A, U, V].to) >> p >> S.P.unit(S.M.associator[B, U, V].from)
      trace[A, B, U * V](p) =?= trace[A, B, U](trace[A * U, B * U, V](inner))
    }

    /** *tr*(*α* ⨾ (*g* ⊗ *p*) ⨾ *α*⁻¹) = *g* ⊗ *tr*(*p*) for pure *g*
      */
    def superposing[A: Obj, B: Obj, C: Obj, D: Obj, U: Obj](
      g: C --> D,
      p: P[A * U, B * U],
    )(using P[C * A, D * B] is Observable): Boolean = {
      val lhs = S.P.unit(S.M.associator[C, A, U].to) >> S.right[C, D, A * U](S.P.unit(g)) >>
        S.left[A * U, B * U, D](p) >> S.P.unit(S.M.associator[D, B, U].from)
      trace[C * A, D * B, U](lhs) =?= (S.right[C, D, A](S.P.unit(g)) >> S.left[A, B, D](trace(p)))
    }

    /** *tr*(*β*) = *id*
      */
    def yanking[U: Obj](using P[U, U] is Observable): Boolean = {
      trace[U, U, U](S.P.unit(S.M.braid[U, U])) =?= S.P.identity[U]
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

  /** The trace of an iteration: *tr*(*p*) = *ι*₁ ⨾ (*p* ⨾ (*id* + *ι*₂))†, a loop that starts on the left. */
  open class OfElgot(tracked val E: Elgot) extends Traced(E.S) {
    import S.M.{+, given}
    import S.P.{P, >>}
    import S.P.K.Obj

    def trace[A: Obj, B: Obj, U: Obj](p: P[A + U, B + U]): P[A, B] = {
      val step = p >> S.P.unit(S.M.tensor(S.P.K.identity[B], S.M.inr[A, U]))
      S.P.unit(S.M.inl[A, U]) >> E.iterate[B, A + U](step)
    }
  }

  /** The trace of a parameterized fixed point: *tr*(*p*) = ((*id* × *π*₂) ⨾ *p*)† ⨾ *π*₁. */
  open class OfConway(tracked val C: Conway) extends Traced(C.S) {
    import S.M.{`*`, given}
    import S.P.{P, >>}
    import S.P.K.Obj

    def trace[A: Obj, B: Obj, U: Obj](p: P[A * U, B * U]): P[A, B] = {
      val step = S.P.unit(S.M.tensor(S.P.K.identity[A], S.M.snd[B, U])) >> p
      C.fix[A, B * U](step) >> S.P.unit(S.M.fst[B, U])
    }
  }
}
