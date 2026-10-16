package parrot
package category

import category.Enriched.over
import category.Profunctor.on

/** The Kleisli profunctor of a functor *F* on **Type**, where
  *   - *K*[*A*, *B*] = *A* → *F*[*B*] is the object part
  *   - *K*(*f*, *g*) = *f* ⨾ - ⨾ *F*(*g*) is the morphism part
  */
type Kleisli[F[_]] = [A, B] =>> A => F[B]

object Kleisli {

  /** Every functor *F* induces a Kleisli profunctor *K* on **Type**, where
    *   - *K*[*A*, *B*] = *A* → *F*[*B*] is the object part
    *   - *K*(*f*, *g*) = *f* ⨾ - ⨾ *F*(*g*) is the morphism part
    */
  given KleisliIsProfunctor: [F[_]: Functor] => Kleisli[F] is Profunctor on Function = new Profunctor {
    type Self[A, B] = A => F[B]
    type On         = Function

    override given ProfunctorOnPromonad: Promonad.FunctionIsPromonad.type = Promonad.FunctionIsPromonad
    override val OnIsPromonad: Promonad.FunctionIsPromonad.type          = Promonad.FunctionIsPromonad

    def dimap[A, B, C, D](f: C => A, g: B => D)(p: A => F[B]): C => F[D] = {
      c => p(f(c)).map(g)
    }
  }

  /** Every monad *M* induces a Kleisli promonad *K* on **Type**, where
    *   - *K*[*A*, *B*] = *A* → *M*[*B*] are the morphisms
    *   - *η*(*f*) = *f* ⨾ *η*' is the unit
    *   - *μ*(*q*, *p*) = *p* ⨾ *M*(*q*) ⨾ *μ*' = *a* ↦ *p*(*a*) >>= *q* is the multiplication
    *
    * Here *η*' and *μ*' are the unit and the multiplication of *F*.
    */
  given KleisliIsPromonad: [M[_]: Monad] => Kleisli[M] is Promonad on Function = new Promonad {
    type Self[A, B] = A => M[B]
    type On         = Function

    override given ProfunctorOnPromonad: Promonad.FunctionIsPromonad.type = Promonad.FunctionIsPromonad
    override val OnIsPromonad: Promonad.FunctionIsPromonad.type          = Promonad.FunctionIsPromonad

    def unit[A, B](f: A => B): A => M[B] = {
      a => M.unit(f(a))
    }

    def multiply[A, B, C](q: B => M[C], p: A => M[B]): A => M[C] = {
      a => p(a).flatMap(q)
    }
  }

  /** Every functor *F* induces a cartesian strong Kleisli profunctor *K* on **Type**, where
    *   - *first*(*p*) = (*a*, *c*) ↦ *F*(− × *c*)(*p*(*a*)) is the left strength
    *   - *second*(*p*) = (*c*, *a*) ↦ *F*(*c* × −)(*p*(*a*)) is the right strength
    */
  given KleisliIsStrong: [F[_]: Functor] => Kleisli[F] is Strong.on[Function, Unit, Tuple2] = new Strong {
    type Self[A, B] = A => F[B]

    override given StrongProfunctor: (Kleisli[F] is Profunctor on Function) = KleisliIsProfunctor[F]
    override val SelfIsProfunctor: Kleisli[F] is Profunctor on Function = KleisliIsProfunctor[F]
    override val OnIsMonoidal: Monoidal.FunctionIsMonoidal.type         = Monoidal.FunctionIsMonoidal

    def first[A, B, C](p: A => F[B]): ((A, C)) => F[(B, C)] = {
      (a, c) => p(a).map((_, c))
    }

    def second[A, B, C](p: A => F[B]): ((C, A)) => F[(C, B)] = {
      (c, a) => p(a).map((c, _))
    }
  }

  /** The Kleisli promonad inherits the coproducts of **Type**, where
    *   - *ι*₁ = *a* ↦ *η*(Left(*a*)) is the left injection
    *   - *ι*₂ = *b* ↦ *η*(Right(*b*)) is the right injection
    *   - [*f*, *g*] = *e* ↦ *e*.fold(*f*, *g*) is the copairing morphism
    *   - *absurd* = *id* is the unique morphism from the initial object
    *
    * Here *η* is the unit of *F*.
    */
  given KleisliIsCocartesian: [M[_]: Monad] => Kleisli[M] is Cocartesian.`with`[Nothing, Either] = new Cocartesian {
    type Self[A, B] = A => M[B]
    type Z          = Nothing
    type Tensor     = Either

    override given CocartesianPromonad: Kleisli[M] is Promonad on Function = KleisliIsPromonad[M]

    def absurd[A]: Nothing => M[A] = {
      n => n
    }

    def left[A, B]: A => M[Either[A, B]] = {
      a => M.unit(Left(a))
    }

    def right[A, B]: B => M[Either[A, B]] = {
      b => M.unit(Right(b))
    }

    def sum[A, B, C](f: A => M[C], g: B => M[C]): Either[A, B] => M[C] = {
      _.fold(f, g)
    }
  }

  /** Hom-sets are function types and thus have fixed points by eta-expansion: fix(*f*) = *g* where *g* = *f*(*a* ↦
    * *g*(*a*)).
    */
  given KleisliIsFixedEnriched: [M[_]: Monad] => Kleisli[M] is Enriched over Fixed.in[Function, Unit, LazyTuple2, Function] = new Enriched {
    type Self[A, B] = A => M[B]
    type Over       = Fixed.in[Function, Unit, LazyTuple2, Function]

    override given EnrichedPromonad: Kleisli[M] is Promonad on Function = KleisliIsPromonad[M]

    override given HomIsV: [A, B] => ((A => M[B]) is Fixed.in[Function, Unit, LazyTuple2, Function]) = Fixed.FunctionIsFixed[A, M[B]]
  }

  /** Every restriction monad *M* induces a restriction Kleisli promonad, where
    *   - *p̄* = *a* ↦ *F*(_ ↦ *a*)(*p*(*a*)̄') is the restriction operation
    *
    * Here *m̄'* is the restriction operation of *M*.\
    */
  given KleisliIsRestriction: [M[_]: RestrictionMonad] => Kleisli[M] is Restriction = {
    import M.SelfIsMonad.SelfIsFunctor.*

    given M.SelfIsMonad.type = M.SelfIsMonad

    new Restriction {
      type Self[A, B] = A => M[B]

      override given RestrictionPromonad: Kleisli[M] is Promonad on Function = KleisliIsPromonad[M]

      def restrict[A, B](p: A => M[B]): A => M[A] = {
        a => p(a).restrict.map(_ => a)
      }
    }
  }

  given KleisliIsValuedEnriched
    : [M[_]: {Monad, Valued as V}] => (P: V.V is Pointwise) => Kleisli[M] is Enriched over V.V =
    new Enriched {
      type Self[A, B] = A => M[B]
      type Over       = V.V

      override given EnrichedPromonad: Kleisli[M] is Promonad on Function = KleisliIsPromonad[M]

      override given HomIsV: [A, B] => ((A => M[B]) is V) = {
        P.FunctionIsV[A, M[B]]
      }
    }

  /** Every Elgot monad *M* induces an Elgot iteration on the Kleisli category, where
    *   - *p*† = *p*†' is the iteration operation
    *
    * Here *p*†' is the iteration operation of *M*.
    */
  given KleisliIsElgot: [F[_]: ElgotMonad] => Kleisli[F] is Elgot.`with`[Nothing, Either] = {
    given F.SelfIsMonad.type = F.SelfIsMonad

    new Elgot {
      type Self[A, B] = A => F[B]

      override given ElgotCocartesian: Kleisli[F] is Cocartesian.`with`[Nothing, Either] = KleisliIsCocartesian[F]
      override val SelfIsCocartesian: Kleisli[F] is Cocartesian.`with`[Nothing, Either] = ElgotCocartesian

      def dagger[A, C](p: C => F[Either[A, C]]): C => F[A] = {
        F.iterate(p)
      }
    }
  }
}
