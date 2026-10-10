package parrot
package category

import Enriched.over
import Profunctor.on

/** The Kleisli profunctor of a monad *F* over **Type**, where
  *   - *K*[*A*, *B*] = *A* → *F*[*B*] is the object part
  *   - *K*(*f*, *g*) = *f* ⨾ - ⨾ *F*(*g*) is the morphism part
  *
  * Further structure of *F* lifts to further structure of *K*:
  *   - every monad induces a promonad (the Kleisli category), a strong profunctor and coproducts
  *   - a `Monad.Plus` induces an enrichment of the Kleisli category in additive monoids
  *   - a `Monad.Restriction` induces a restriction category
  *   - a `Monad.Elgot` induces an Elgot iteration
  */
type Kleisli[F[_]] = [A, B] =>> A => F[B]

object Kleisli {

  /** The Kleisli category of *F*: *η*(*f*) = *f* ⨾ *η*', *μ*(*q*, *p*) = *a* ↦ *p*(*a*) >>= *q*. */
  given KleisliIsPromonad: [F[_]] => (F: F is Monad) => (Kleisli[F] is Promonad on Function) = new Promonad {
    type Self[A, B] = A => F[B]
    type On         = Function

    override val OnIsPromonad: Promonad.FunctionIsPromonad.type = Promonad.FunctionIsPromonad

    def unit[A, B](f: A => B): A => F[B] = a => F.unit(f(a))

    def multiply[A, B, C](q: B => F[C], p: A => F[B]): A => F[C] = a => F.flatMap(p(a))(q)
  }

  /** Every monad on **Type** is strong: *first*(*p*) = (*a*, *c*) ↦ *F*(− × *c*)(*p*(*a*)). */
  given KleisliIsStrong: [F[_]] => (F: F is Monad) => (Kleisli[F] is Strong.on[Function, Unit, Tuple2]) = new Strong {
    type Self[A, B] = A => F[B]
    type On         = Function

    override val OnIsPromonad: Promonad.FunctionIsPromonad.type = Promonad.FunctionIsPromonad
    override val OnIsMonoidal: Monoidal.FunctionIsMonoidal.type = Monoidal.FunctionIsMonoidal

    def dimap[A, B, C, D](f: C => A, g: B => D)(p: A => F[B]): C => F[D] = c => F.map(p(f(c)))(g)

    def first[A, B, C](p: A => F[B]): ((A, C)) => F[(B, C)] = (a, c) => F.map(p(a))((_, c))

    def second[A, B, C](p: A => F[B]): ((C, A)) => F[(C, B)] = (c, a) => F.map(p(a))((c, _))
  }

  /** The Kleisli category inherits the coproducts of **Type**: *ι*ᵢ = *η* ∘ *ι*ᵢ', [*f*, *g*] = *f* + *g* folded. */
  given KleisliIsCocartesian: [F[_]] => (F: F is Monad) => (Kleisli[F] is Cocartesian.`with`[Nothing, Either]) =
    new Cocartesian {
      type Self[A, B] = A => F[B]
      type Z          = Nothing
      type Tensor     = Either

      override val SelfIsPromonad: Kleisli[F] is Promonad = KleisliIsPromonad[F]

      def absurd[A]: Nothing => F[A] = n => n

      def left[A, B]: A => F[Either[A, B]] = a => F.unit(Left(a))

      def right[A, B]: B => F[Either[A, B]] = b => F.unit(Right(b))

      def sum[A, B, C](f: A => F[C], g: B => F[C]): Either[A, B] => F[C] = _.fold(f, g)
    }

  /** Hom-sets are additive monoids pointwise: 0 = *a* ↦ 0', *p* + *q* = *a* ↦ *p*(*a*) +' *q*(*a*). */
  given KleisliIsEnriched: [F[_]] => (F: F is Monad.Plus) => (Kleisli[F] is Enriched over Monoid.Additive) =
    new Enriched {
      type Self[A, B] = A => F[B]
      type Over       = Monoid.Additive

      override val SelfIsPromonad: Kleisli[F] is Promonad = KleisliIsPromonad[F]

      override given HomIsV: [A, B] => ((A => F[B]) is Monoid.Additive) = new Monoid.Additive {
        type Self = A => F[B]

        def zero: A => F[B] = _ => F.zero

        def plus(p: A => F[B], q: A => F[B]): A => F[B] = a => F.plus(p(a))(q(a))
      }
    }

  /** The restriction of *p* keeps the definedness of *p*(*a*) and returns *a*: p̄ = *a* ↦ *F*(_ ↦ *a*)(*p*(*a*)‾'). */
  given KleisliIsRestriction: [F[_]] => (F: F is Monad.Restriction) => (Kleisli[F] is Restriction on Function) =
    new Restriction {
      type Self[A, B] = A => F[B]
      type On         = Function

      override val OnIsPromonad: Promonad.FunctionIsPromonad.type = Promonad.FunctionIsPromonad

      def unit[A, B](f: A => B): A => F[B] = a => F.unit(f(a))

      def multiply[A, B, C](q: B => F[C], p: A => F[B]): A => F[C] = a => F.flatMap(p(a))(q)

      def restrict[A, B](p: A => F[B]): A => F[A] = a => F.map(F.restrict(p(a)))(_ => a)
    }

  /** The Elgot iteration of the Kleisli category is the iteration of *F*: *p*† = *p*†'. */
  given KleisliIsElgot: [F[_]] => (F: F is Monad.Elgot) => (Kleisli[F] is Elgot.on[Function, Nothing, Either]) =
    new Elgot {
      type Self[A, B] = A => F[B]
      type On         = Function

      override val OnIsPromonad: Promonad.FunctionIsPromonad.type          = Promonad.FunctionIsPromonad
      override val OnIsCocartesian: Cocartesian.FunctionIsCocartesian.type = Cocartesian.FunctionIsCocartesian

      def unit[A, B](f: A => B): A => F[B] = a => F.unit(f(a))

      def multiply[A, B, C](q: B => F[C], p: A => F[B]): A => F[C] = a => F.flatMap(p(a))(q)

      def dagger[A, C](p: C => F[Either[A, C]]): C => F[A] = F.iterate(p)
    }
}
