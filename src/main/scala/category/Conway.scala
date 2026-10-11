package parrot
package category

import scala.annotation.targetName

/** A Conway promonad on an underlying category **C**.
  *
  * Represents a promonad *P* whose induced category is cartesian with unit *I* and tensor ⊗ and is equipped with a
  * parameterized Conway fixed-point operator, where
  *   - _†: *P*[*A* ⊗ *C*, *C*] → *P*[*A*, *C*] is the parameterized Conway fixed-point operation.
  *
  * @note Every Conway structure induces a cartesian traced promonad.
  */
trait Conway {
  type Self[_, _]: Cartesian

  val SelfIsCartesian: Self is Cartesian = summon
  import SelfIsCartesian.*
  import SelfIsCartesian.SelfIsPromonad.*

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

    /** Fixed-point property: *f*† = *f* ∘ ⟨*id*, *f*†⟩ */
    def fixedPoint[A, C](f: (A * C) ~> C)(using (A ~> C) is Eq): Boolean = {
      ((identity[A] &&& f.dagger) >>> f) === f.dagger
    }

    /** Parameter naturality: (*f* ∘ (*h* ⊗ *id*))† = *f*† ∘ *h* */
    def parameterNaturality[A0, A, C](f: (A * C) ~> C, h: A0 ==> A)(using (A0 ~> C) is Eq): Boolean = {
      ((unit(h) *** identity[C]) >>> f).dagger === (unit(h) >>> f.dagger)
    }

    /** Composition identity (dinaturality): *g* ∘ (*f* ∘ (*id* ⊗ *g*))† = (*g* ∘ *f*)† */
    def composition[A, C, D](f: (A * C) ~> D, g: D ==> C)(using (A ~> C) is Eq): Boolean = {
      (f >>> unit(g)).dagger === (((identity[A] *** unit(g)) >>> f).dagger >>> unit(g))
    }

    /** Double dagger identity (diagonality / Bekić): (*f* ∘ ⟨*id*, π₂⟩)† = (*f*†)† */
    def doubleDagger[A, C](p: ((A * C) * C) ~> C)(using (A ~> C) is Eq): Boolean = {
      ((identity[A * C] &&& second[A, C]) >>> p).dagger === p.dagger.dagger
    }
  }
}

object Conway {

  /** Refines the products of `Conway` to the terminal object `U` and product `T`. */
  type `with`[U, T[_, _]] = Conway { val SelfIsCartesian: Cartesian.`with`[U, T] }

  /** Summons the `Conway` instance of `P`. */
  def apply[P[_, _]: Conway]: P is Conway = summon

  /** Every Conway promonad induces a cartesian traced promonad, where trace is derived from the Conway dagger operator:
    * *tr*(*p*) = π₁ ∘ (*p* ∘ (*id* ⊗ π₂))†
    */
  given ConwayIsCartesianTraced: [P[_, _]] => (
    C: P is Conway,
    K: C.SelfIsCartesian.SelfIsPromonad.On is Cartesian.`with`[C.SelfIsCartesian.I, C.SelfIsCartesian.Tensor],
  ) => P is Traced.on[C.SelfIsCartesian.SelfIsPromonad.On, C.SelfIsCartesian.I, C.SelfIsCartesian.Tensor] =
    new Traced {
      type Self[A, B] = P[A, B]

      override given given_Profunctor_Self: C.SelfIsCartesian.SelfIsPromonad.type = C.SelfIsCartesian.SelfIsPromonad
      override val SelfIsProfunctor: C.SelfIsCartesian.SelfIsPromonad.type        = C.SelfIsCartesian.SelfIsPromonad
      override val OnIsMonoidal: K.type                                           = K
      import OnIsMonoidal.*
      import SelfIsProfunctor.*

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

  /** Every cartesian traced promonad induces a Conway structure, where dagger is derived from the trace operator as:
    * *p*† = *tr*(Δ ∘ *p*)
    */
  given CartesianTracedIsConway: [P[_, _]] => (
    C: P is Cartesian,
    T: P is Traced.on[C.SelfIsPromonad.On, C.I, C.Tensor],
  ) => P is Conway.`with`[C.I, C.Tensor] = new Conway {
    type Self[A, B] = P[A, B]

    override val SelfIsCartesian: C.type = C
    import C.*
    import C.SelfIsPromonad.*

    def dagger[A, X](p: (A * X) ~> X): A ~> X = {
      T.left[A, X, X](p >>> diagonal[X])
    }
  }

  /** `Function` is a `Conway` category under lazy tuple products via knot-tying fixed points. */
  given FunctionIsLazyCartesianConway: Function is Conway {
    override given given_Cartesian_Self: Cartesian.FunctionIsLazyCartesian.type = Cartesian.FunctionIsLazyCartesian
    override val SelfIsCartesian: Cartesian.FunctionIsLazyCartesian.type        = Cartesian.FunctionIsLazyCartesian

    def dagger[A, C](p: LazyTuple2[A, C] => C): A => C = {
      a =>
        {
          lazy val c: C = p(LazyTuple2(a, c))
          c
        }
    }
  }
}
