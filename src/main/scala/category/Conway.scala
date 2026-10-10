package parrot
package category

import scala.annotation.targetName

/** A Conway structure on a promonad over an underlying cartesian category **C**.
  *
  * Represents a promonad *P* that is strong with respect to a cartesian category (**C**, ⊗, *I*) and equipped with a
  * parameterized Conway fixed-point operator, where
  *   - _†: *P*[*A* ⊗ *C*, *C*] → *P*[*A*, *C*] is the parameterized Conway fixed-point operation.
  *
  * The products are those of **C**, acting on *P* through its strength, rather than products of the category induced
  * by *P*: effectful categories (e.g. Kleisli categories) are only premonoidal, but still admit fixed points.
  *
  * @note Conway promonads in a cartesian setting are equivalent to cartesian traced promonads.
  * @see [[Fixed]] for the unparameterized fixed points on exponentials of a cartesian closed category.
  */
trait Conway {
  type Self[_, _]: Promonad

  val SelfIsPromonad: Self is Promonad = summon
  import SelfIsPromonad.*

  /** The cartesian structure of the underlying category **C**. */
  val OnIsCartesian: SelfIsPromonad.On is Cartesian
  import OnIsCartesian.{&&&, ***, `*`, diagonal, second}

  /** The strength of *P* with respect to the cartesian structure of **C**. */
  val SelfIsStrong: Self is Strong.on[SelfIsPromonad.On, OnIsCartesian.I, OnIsCartesian.Tensor]

  /** Maps a morphism *p*: *A* ⊗ *C* ~> *C* to its Conway fixed-point morphism *p*†: *A* ~> *C*. */
  def dagger[A, C](p: (A * C) ~> C): A ~> C

  extension [A, C](p: (A * C) ~> C)
    /** Infix extension for [[dagger]]. */
    @targetName("daggerExt")
    def dagger(using DummyImplicit): A ~> C = {
      Conway.this.dagger(p)
    }

  /** Laws that any `Conway` must satisfy. */
  object ConwayLaws {

    /** Fixed-point property: *f*† = *f* ∘ ⟨*id*, *f*†⟩, where ⟨*id*, *f*†⟩ = *second*(*f*†) ∘ Δ
      */
    def fixedPoint[A, C](p: (A * C) ~> C)(using (A ~> C) is Eq): Boolean = {
      (unit(diagonal[A]) >>> SelfIsStrong.second[A, C, A](p.dagger) >>> p) === p.dagger
    }

    /** Parameter naturality: (*f* ∘ (*h* ⊗ *id*))† = *f*† ∘ *h*
      */
    def parameterNaturality[A0, A, C](p: (A * C) ~> C, h: A0 ==> A)(
      using (A0 ~> C) is Eq,
    ): Boolean = {
      p.lmap(h *** OnIsPromonad.identity[C]).dagger === (unit(h) >>> p.dagger)
    }

    /** Composition identity (dinaturality): (*f* ∘ (*id* ⊗ *g*))† ∘ *g* = (*f* ∘ *g*)†
      */
    def composition[A, C, D](p: (A * C) ~> D, g: D ==> C)(
      using (A ~> C) is Eq,
    ): Boolean = {
      (p >>> unit(g)).dagger === (p.lmap(OnIsPromonad.identity[A] *** g).dagger >>> unit(g))
    }

    /** Double dagger identity (diagonality / Bekić): (*f* ∘ ⟨*id*, π₂⟩)† = (*f*†)†
      */
    def doubleDagger[A, C](p: ((A * C) * C) ~> C)(
      using (A ~> C) is Eq,
    ): Boolean = {
      val step: (A * C) ==> ((A * C) * C) = OnIsPromonad.identity[A * C] &&& second[A, C]
      p.lmap(step).dagger === p.dagger.dagger
    }
  }
}

object Conway {

  /** Refines the products of `Conway` to the unit `U` and product `T`. */
  type `with`[U, T[_, _]] = Conway { val OnIsCartesian: Cartesian.`with`[U, T] }

  /** Summons the `Conway` instance of `P`. */
  def apply[P[_, _]: Conway]: P is Conway = summon

  /** Every Conway promonad on an underlying cartesian category induces a cartesian traced promonad, where trace is
    * derived from the Conway dagger operator: `trace(p) = π₁ ∘ (p ∘ (id ⊗ π₂))†`
    */
  given ConwayIsCartesianTraced: [P[_, _]] => (C: P is Conway)
    => P is Traced.on[C.SelfIsPromonad.On, C.OnIsCartesian.I, C.OnIsCartesian.Tensor] = new Traced {
    type Self[A, B] = P[A, B]

    override given given_Profunctor_Self: C.SelfIsPromonad.type = C.SelfIsPromonad
    override val SelfIsProfunctor: C.SelfIsPromonad.type        = C.SelfIsPromonad
    override val OnIsMonoidal: C.OnIsCartesian.type             = C.OnIsCartesian
    import SelfIsProfunctor.{dimap, lmap, rmap, ~>, OnIsPromonad}
    import OnIsMonoidal.{&&&, ***, `*`, first, second}

    def left[A, B, C0](p: (A * C0) ~> (B * C0)): A ~> B = {
      val f    = OnIsPromonad.identity[A] *** second[B, C0]
      val step = lmap(f)(p)
      rmap(first[B, C0])(C.dagger(step))
    }

    def right[A, B, C0](p: (C0 * A) ~> (C0 * B)): A ~> B = {
      val braidIn  = second[A, C0] &&& first[A, C0]
      val braidOut = second[C0, B] &&& first[C0, B]
      left(dimap(braidIn, braidOut)(p))
    }
  }

  /** Every strong and traced promonad over a cartesian category induces a Conway promonad, where dagger is derived from
    * the trace operator: `p† = trace(p ∘ Δ)`
    */
  given CartesianTracedIsConway: [P[_, _]] => (
    P: P is Promonad,
    C: P.On is Cartesian,
    S: P is Strong.on[P.On, C.I, C.Tensor],
    T: P is Traced.on[P.On, C.I, C.Tensor],
  ) => P is Conway.`with`[C.I, C.Tensor] = new Conway {
    type Self[A, B] = P[A, B]

    override val SelfIsPromonad: P.type = P
    override val OnIsCartesian: C.type  = C
    override val SelfIsStrong: S.type   = S
    import P.{rmap, ~>}
    import C.{`*`, diagonal}

    def dagger[A, X](p: (A * X) ~> X): A ~> X = {
      val step = rmap(diagonal[X])(p)
      T.left[A, X, X](step)
    }
  }

  /** `Function` is a `Conway` promonad under lazy tuple products via knot-tying fixed points. */
  given FunctionIsLazyCartesianConway: Function is Conway {
    override val SelfIsPromonad: Promonad.FunctionIsPromonad.type = Promonad.FunctionIsPromonad
    override val OnIsCartesian: Cartesian.FunctionIsLazyCartesian.type = Cartesian.FunctionIsLazyCartesian
    override val SelfIsStrong: Strong.FunctionIsLazyStrong.type     = Strong.FunctionIsLazyStrong

    def dagger[A, C](p: LazyTuple2[A, C] => C): A => C = {
      a =>
        {
          lazy val c: C = p(LazyTuple2(a, c))
          c
        }
    }
  }
}
