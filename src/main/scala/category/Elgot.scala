package parrot
package category

import scala.annotation.targetName

/** An Elgot structure on a category with coproducts.
  *
  * Represents a promonad *P* whose induced category has coproducts (⊕, *Z*) and is equipped with an Elgot fixed-point
  * (iteration) operator, where
  *   - _†: *P*[*C*, *A* ⊕ *C*] → *P*[*C*, *A*] is the Elgot fixed-point (iteration) operation.
  *
  * @note In a cocartesian setting, every Elgot structure induces a cocartesian traced promonad.
  */
trait Elgot {
  type Self[_, _]: Cocartesian

  val SelfIsCocartesian: Self is Cocartesian = summon
  import SelfIsCocartesian.{+, +++, |||, right}
  import SelfIsCocartesian.SelfIsPromonad.{==>, identity, unit, ~>, >>>}

  /** Maps a morphism *p*: *C* ~> *A* ⊕ *C* to its Elgot fixed-point morphism *p*†: *C* ~> *A*. */
  def dagger[A, C](p: C ~> (A + C)): C ~> A

  extension [A, C](p: C ~> (A + C))
    /** Infix extension for [[dagger]]. */
    @targetName("daggerExt")
    def dagger(using DummyImplicit): C ~> A = {
      Elgot.this.dagger(p)
    }

  /** Laws that any `Elgot` must satisfy. */
  object ElgotLaws {

    /** Fixed-point property (unfolding): *f*† = [*id*, *f*†] ∘ *f*
      */
    def fixedPoint[A, C](p: C ~> (A + C))(using (C ~> A) is Eq): Boolean = {
      (p >>> (identity[A] ||| p.dagger)) === p.dagger
    }

    /** Parameter naturality: ((*h* ⊕ *id*) ∘ *f*)† = *h* ∘ *f*†
      */
    def parameterNaturality[A, B, C](p: C ~> (A + C), h: A ==> B)(
      using (C ~> B) is Eq,
    ): Boolean = {
      (p >>> (unit(h) +++ identity[C])).dagger === (p.dagger >>> unit(h))
    }

    /** Composition identity (dinaturality): (*g* ∘ *f*)† = *g* ∘ ((*id* ⊕ *g*) ∘ *f*)†
      */
    def composition[A, C, D](p: D ~> (A + C), g: C ==> D)(
      using (C ~> A) is Eq,
    ): Boolean = {
      (unit(g) >>> p).dagger === (unit(g) >>> (p >>> (identity[A] +++ unit(g))).dagger)
    }

    /** Double dagger identity (codiagonality / Bekić): (*f*†)† = ([*id*, ι₂] ∘ *f*)†
      */
    def doubleDagger[A, C](p: C ~> ((A + C) + C))(
      using (C ~> A) is Eq,
    ): Boolean = {
      (p >>> (identity[A + C] ||| right[A, C])).dagger === p.dagger.dagger
    }

    /** Uniformity law (Plotkin's principle): if (*id* ⊕ *h*) ∘ *f* = *g* ∘ *h*, then *f*† = *g*† ∘ *h*
      */
    def uniformity[A, C, C0](f: C ~> (A + C), g: C0 ~> (A + C0), h: C ==> C0)(
      using
      (C ~> (A + C0)) is Eq,
      (C ~> A) is Eq
    ): Boolean = {
      val sim = (f >>> (identity[A] +++ unit(h))) === (unit(h) >>> g)
      if sim then f.dagger === (unit(h) >>> g.dagger) else true
    }
  }
}

object Elgot {

  /** Refines the coproducts of `Elgot` to the initial object `U` and coproduct `T`. */
  type `with`[U, T[_, _]] = Elgot { val SelfIsCocartesian: Cocartesian.`with`[U, T] }

  /** Summons the `Elgot` instance of `P`. */
  def apply[P[_, _]: Elgot]: P is Elgot = summon

  /** Every Elgot structure whose coproducts are inherited from the underlying category induces a cocartesian traced
    * promonad, where trace is derived from the Elgot dagger operator: `trace(p) = ((p ∘ (id ⊕ ι₂))†) ∘ ι₁`
    */
  given ElgotIsCocartesianTraced: [P[_, _]] => (E: P is Elgot) => (
    K: E.SelfIsCocartesian.SelfIsPromonad.On is Cocartesian.`with`[E.SelfIsCocartesian.Z, E.SelfIsCocartesian.Tensor]
  ) => P is Traced.on[E.SelfIsCocartesian.SelfIsPromonad.On, E.SelfIsCocartesian.Z, E.SelfIsCocartesian.Tensor] =
    new Traced {
      type Self[A, B] = P[A, B]

      override given given_Profunctor_Self: E.SelfIsCocartesian.SelfIsPromonad.type = E.SelfIsCocartesian.SelfIsPromonad
      override val SelfIsProfunctor: E.SelfIsCocartesian.SelfIsPromonad.type        = E.SelfIsCocartesian.SelfIsPromonad
      override val OnIsMonoidal: K.type                                             = K
      import SelfIsProfunctor.{dimap, lmap, rmap, ~>, OnIsPromonad}
      import OnIsMonoidal.{+, +++, |||}

      def left[A, B, C0](p: (A + C0) ~> (B + C0)): A ~> B = {
        val g    = OnIsPromonad.identity[B] +++ K.right[A, C0]
        val step = rmap(g)(p)
        lmap(K.left[A, C0])(E.dagger(step))
      }

      def right[A, B, C0](p: (C0 + A) ~> (C0 + B)): A ~> B = {
        val braidIn  = K.right[C0, A] ||| K.left[C0, A]
        val braidOut = K.right[B, C0] ||| K.left[B, C0]
        left(dimap(braidIn, braidOut)(p))
      }
    }

  /** Every cocartesian and traced promonad induces an Elgot structure, where dagger is derived from the trace operator:
    * `p† = trace(p ∘ ∇)`
    */
  given CocartesianTracedIsElgot: [P[_, _]] => (
    C: P is Cocartesian,
    T: P is Traced.on[C.SelfIsPromonad.On, C.Z, C.Tensor],
  ) => P is Elgot.`with`[C.Z, C.Tensor] = new Elgot {
    type Self[A, B] = P[A, B]

    override val SelfIsCocartesian: C.type = C
    import C.{+, fold}
    import C.SelfIsPromonad.{~>, >>>}

    def dagger[A, X](p: X ~> (A + X)): X ~> A = {
      T.left[X, A, X](fold[X] >>> p)
    }
  }

  /** `Function` is an `Elgot` category under disjoint sum coproducts via tail-recursive iteration. */
  given FunctionIsCocartesianElgot: Function is Elgot {
    override val SelfIsCocartesian: Cocartesian.FunctionIsCocartesian.type = Cocartesian.FunctionIsCocartesian

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
