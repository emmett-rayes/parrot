package parrot
package category

import scala.annotation.targetName

/** An Elgot promonad on an underlying cocartesian category **C**.
  *
  * Represents a promonad *P* equipped with an Elgot fixed-point (iteration) operator with respect to a cocartesian
  * category (**C**, ⊕, *Z*), where
  *   - _†: *P*[*C*, *A* ⊕ *C*] → *P*[*C*, *A*] is the Elgot fixed-point (iteration) operation.
  *
  * @note In a cocartesian setting, every Elgot promonad induces a cocartesian traced promonad.
  */
trait Elgot extends Promonad {
  type Self[_, _]

  override type On[_, _]: {Promonad, Cocartesian}

  val OnIsCocartesian: On is Cocartesian
  import OnIsCocartesian.*

  /** Maps a morphism *p*: *C* ~> *A* ⊕ *C* to its Elgot fixed-point morphism *p*†: *C* ~> *A*. */
  def dagger[A, C](p: C ~> (A + C)): C ~> A

  extension [A, C](p: C ~> (A + C))
    /** Infix extension for [[dagger]]. */
    @targetName("daggerExt")
    def dagger(using DummyImplicit): C ~> A = {
      Elgot.this.dagger(p)
    }

  /** Laws that any `Elgot` promonad must satisfy. */
  object ElgotLaws {

    /** Fixed-point property (unfolding): *f*† = [*id*, *f*†] ∘ *f*
      */
    def fixedPoint[A, C](p: C ~> (A + C))(
      using
      C: Self is Cocartesian.`with`[?, OnIsCocartesian.Tensor],
      eq: (C ~> A) is Eq,
    ): Boolean = {
      val copair: (A + C) ~> A = identity[A] ||| p.dagger
      (p >>> copair) === p.dagger
    }

    /** Parameter naturality: ((*h* ⊕ *id*) ∘ *f*)† = *h* ∘ *f*†
      */
    def parameterNaturality[A, B, C](p: C ~> (A + C), h: A ==> B)(
      using (C ~> B) is Eq,
    ): Boolean = {
      p.rmap(h +++ OnIsPromonad.identity[C]).dagger === (p.dagger >>> unit(h))
    }

    /** Composition identity (dinaturality): (*g* ∘ *f*)† = *g* ∘ ((*id* ⊕ *g*) ∘ *f*)†
      */
    def composition[A, C, D](p: D ~> (A + C), g: C ==> D)(
      using (C ~> A) is Eq,
    ): Boolean = {
      (unit(g) >>> p).dagger === (unit(g) >>> p.rmap(OnIsPromonad.identity[A] +++ g).dagger)
    }

    /** Double dagger identity (codiagonality / Bekić): (*f*†)† = ([*id*, ι₂] ∘ *f*)†
      */
    def doubleDagger[A, C](p: C ~> ((A + C) + C))(
      using (C ~> A) is Eq,
    ): Boolean = {
      val step: ((A + C) + C) ==> (A + C) =
        OnIsPromonad.identity[A + C] ||| OnIsCocartesian.right[A, C]
      p.rmap(step).dagger === p.dagger.dagger
    }

    /** Uniformity law (Plotkin's principle): if (*id* ⊕ *h*) ∘ *f* = *g* ∘ *h*, then *f*† = *g*† ∘ *h*
      */
    def uniformity[A, C, C0](f: C ~> (A + C), g: C0 ~> (A + C0), h: C ==> C0)(
      using
      (C ~> (A + C0)) is Eq,
      (C ~> A) is Eq
    ): Boolean = {
      val sim = f.rmap(OnIsPromonad.identity[A] +++ h) === (unit(h) >>> g)
      if sim then f.dagger === (unit(h) >>> g.dagger) else true
    }
  }
}

object Elgot {

  /** Refines the `On` type of `Elgot` to the cocartesian `K` with initial object `U` and tensor `T`. */
  type on[K[_, _], U, T[_, _]] = Elgot {
    type On = K
    val OnIsCocartesian: K is Cocartesian.`with`[U, T]
  }

  /** Refines the `Z` and `Tensor` types of `Elgot` to `U` and `T`. */
  type `with`[U, T[_, _]] = Elgot { val OnIsCocartesian: Cocartesian.`with`[U, T] }

  /** Summons the `Elgot` instance of `P`. */
  def apply[P[_, _]: Elgot]: P is Elgot = summon

  /** Every Elgot promonad on an underlying cocartesian category induces a cocartesian traced promonad, where trace is
    * derived from the Elgot dagger operator: `trace(p) = ((p ∘ (id ⊕ ι₂))†) ∘ ι₁`
    */
  given ElgotIsCocartesianTraced
    : [P[_, _]] => (E: P is Elgot) => P is Traced.on[E.On, E.OnIsCocartesian.Z, E.OnIsCocartesian.Tensor] = new Traced {
    type Self = P
    type On   = E.On

    override val OnIsPromonad: E.On is Promonad = E.OnIsPromonad

    export E.dimap

    override val OnIsMonoidal: E.OnIsCocartesian.type = E.OnIsCocartesian
    import OnIsMonoidal.*

    def left[A, B, C0](p: (A + C0) ~> (B + C0)): A ~> B = {
      val g    = E.OnIsPromonad.identity[B] +++ E.OnIsCocartesian.right[A, C0]
      val step = rmap(g)(p)
      lmap(E.OnIsCocartesian.left[A, C0])(E.dagger(step))
    }

    def right[A, B, C0](p: (C0 + A) ~> (C0 + B)): A ~> B = {
      val braidIn  = E.OnIsCocartesian.right[C0, A] ||| E.OnIsCocartesian.left[C0, A]
      val braidOut = E.OnIsCocartesian.right[B, C0] ||| E.OnIsCocartesian.left[B, C0]
      left(dimap(braidIn, braidOut)(p))
    }
  }

  /** Every cocartesian and traced promonad induces an Elgot promonad, where dagger is derived from the trace operator:
    * `p† = trace(p ∘ ∇)`
    */
  given CocartesianTracedIsElgot: [P[_, _]] => (
    P: P is Promonad,
    C: P.On is Cocartesian,
    T: P is Traced.on[P.On, C.Z, C.Tensor],
  ) => P is Elgot.on[P.On, C.Z, C.Tensor] = new Elgot {
    type Self = P
    type On   = P.On

    export P.{Self as _, On as _, *}

    override val OnIsCocartesian: C.type = C
    import OnIsCocartesian.*

    def dagger[A, X](p: X ~> (A + X)): X ~> A = {
      val step = lmap(fold[X])(p)
      T.left[X, A, X](step)
    }
  }

  /** `Function` is an `Elgot` promonad under disjoint sum coproducts via tail-recursive iteration. */
  given FunctionIsCocartesianElgot: Function is Elgot {
    export Promonad.FunctionIsPromonad.*

    override given given_Cocartesian_On: Cocartesian.FunctionIsCocartesian.type = Cocartesian.FunctionIsCocartesian
    override val OnIsCocartesian: Cocartesian.FunctionIsCocartesian.type        = Cocartesian.FunctionIsCocartesian

    def dagger[A, C](p: C => Either[A, C]): C => A = {
      c =>
        {
          @annotation.tailrec
          def loop(curr: C): A = p(curr) match {
            case Left(a)     => a
            case Right(next) => loop(next)
          }
          loop(c)
        }
    }
  }
}
