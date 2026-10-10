package parrot
package category

import scala.annotation.targetName

/** A Conway promonad on an underlying cartesian category **C**.
  *
  * Represents a promonad *P* equipped with a parameterized Conway fixed-point operator with respect to a cartesian
  * category (**C**, ⊗, *I*), where
  *   - _†: *P*[*A* ⊗ *C*, *C*] → *P*[*A*, *C*] is the parameterized Conway fixed-point operation.
  *
  * @note Conway promonads in a cartesian setting are equivalent to cartesian traced promonads.
  */
trait Conway extends Promonad {
  type Self[_, _]

  override type On[_, _]: {Promonad, Cartesian}

  val OnIsCartesian: On is Cartesian
  import OnIsCartesian.*

  /** Maps a morphism *p*: *A* ⊗ *C* ~> *C* to its Conway fixed-point morphism *p*†: *A* ~> *C*. */
  def dagger[A, C](p: (A * C) ~> C): A ~> C

  extension [A, C](p: (A * C) ~> C)
    /** Infix extension for [[dagger]]. */
    @targetName("daggerExt")
    def dagger(using DummyImplicit): A ~> C = {
      Conway.this.dagger(p)
    }

  /** Laws that any `Conway` promonad must satisfy. */
  object ConwayLaws {

    /** Fixed-point property: *f*† = *f* ∘ ⟨*id*, *f*†⟩
      */
    def fixedPoint[A, C](p: (A * C) ~> C)(
      using
      C: Self is Cartesian.`with`[?, OnIsCartesian.Tensor],
      eq: (A ~> C) is Eq,
    ): Boolean = {
      val pair: A ~> (A * C) = identity[A] &&& p.dagger
      (pair >>> p) === p.dagger
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
      val step: (A * C) ==> ((A * C) * C) =
        OnIsPromonad.identity[A * C] &&& OnIsCartesian.second[A, C]
      p.lmap(step).dagger === p.dagger.dagger
    }
  }
}

object Conway {

  /** Refines the `On` type of `Conway` to the cartesian `K` with unit `U` and tensor `T`. */
  type on[K[_, _], U, T[_, _]] = Conway {
    type On = K
    val OnIsCartesian: K is Cartesian.`with`[U, T]
  }

  /** Refines the `I` and `Tensor` types of `Conway` to `U` and `T`. */
  type `with`[U, T[_, _]] = Conway { val OnIsCartesian: Cartesian.`with`[U, T] }

  /** Summons the `Conway` instance of `P`. */
  def apply[P[_, _]: Conway]: P is Conway = summon

  /** Every Conway promonad on an underlying cartesian category induces a cartesian traced promonad, where trace is
    * derived from the Conway dagger operator: `trace(p) = π₁ ∘ (p ∘ (id ⊗ π₂))†`
    */
  given ConwayIsCartesianTraced
    : [P[_, _]] => (C: P is Conway) => P is Traced.on[C.On, C.OnIsCartesian.I, C.OnIsCartesian.Tensor] = new Traced {
    type Self = P
    type On   = C.On

    override val OnIsPromonad: C.On is Promonad = C.OnIsPromonad

    export C.dimap

    override val OnIsMonoidal: C.OnIsCartesian.type = C.OnIsCartesian
    import OnIsMonoidal.*

    def left[A, B, C0](p: (A * C0) ~> (B * C0)): A ~> B = {
      val f    = C.OnIsPromonad.identity[A] *** second[B, C0]
      val step = lmap(f)(p)
      rmap(first[B, C0])(C.dagger(step))
    }

    def right[A, B, C0](p: (C0 * A) ~> (C0 * B)): A ~> B = {
      val braidIn  = second[A, C0] &&& first[A, C0]
      val braidOut = second[C0, B] &&& first[C0, B]
      left(dimap(braidIn, braidOut)(p))
    }
  }

  /** Every cartesian and traced promonad induces a Conway promonad, where dagger is derived from the trace operator:
    * `p† = trace(p ∘ Δ)`
    */
  given CartesianTracedIsConway: [P[_, _]] => (
    P: P is Promonad,
    C: P.On is Cartesian,
    T: P is Traced.on[P.On, C.I, C.Tensor],
  ) => P is Conway.on[P.On, C.I, C.Tensor] = new Conway {
    type Self = P
    type On   = P.On

    export P.{Self as _, On as _, *}

    override val OnIsCartesian: C.type = C
    import OnIsCartesian.*

    def dagger[A, X](p: (A * X) ~> X): A ~> X = {
      val step = rmap(diagonal[X])(p)
      T.left[A, X, X](step)
    }
  }

  /** `Function` is a `Conway` promonad under lazy tuple products via knot-tying fixed points. */
  given FunctionIsLazyCartesianConway: Function is Conway {
    export Promonad.FunctionIsPromonad.*

    override given given_Cartesian_On: Cartesian.FunctionIsLazyCartesian.type = Cartesian.FunctionIsLazyCartesian
    override val OnIsCartesian: Cartesian.FunctionIsLazyCartesian.type        = Cartesian.FunctionIsLazyCartesian

    def dagger[A, C](p: LazyTuple2[A, C] => C): A => C = {
      a =>
        {
          lazy val c: C = p(LazyTuple2(a, c))
          c
        }
    }
  }
}
