package parrot
package category

import Category.Type

/** The Kleisli promonad of a monad *M* on **C**: effectful arrows *A* → *M*[*B*].
  *
  * Represents a promonad over **C**, where
  *   - *P*(*A*,*B*) = **C**(*A*,*M*[*B*])
  *   - *unit*(*f*) = *η* ∘ *f* embeds the pure morphisms
  *   - *multiply*(*g*,*f*) = *g*∘ *f* runs *f*, then *g* on its result
  *
  * @see docs/TUTORIAL.md §15.2
  */
open class Kleisli(tracked val monad: Monad) extends Promonad(monad.category) {
  import monad.category.{Obj, -->}

  type Self[A, B] = A --> monad.M[B]

  private given MIsObj: [A: Obj] => (monad.M[A] is Obj) = monad.objects[A]

  def unit[A: Obj, B: Obj](f: A --> B): A --> monad.M[B] = {
    monad.category.andThen(f, monad.unit[B])
  }

  def multiply[A: Obj, B: Obj, C: Obj](g: B --> monad.M[C], f: A --> monad.M[B]): A --> monad.M[C] = {
    monad.category.andThen(f, monad.bind(g))
  }

  override def identity[A: Obj]: A --> monad.M[A] = {
    monad.unit[A]
  }
}

object Kleisli {

  /** The Kleisli promonad of a monad *M*. */
  type Of[M <: Monad] = Kleisli { val monad: M }

  /** Every Kleisli promonad of a monad on 𝒮 is strong for products, where
    *   - *τ*(*p*) = (*c*,*a*) ↦ *M*(*b* ↦ (*c*,*b*))(*p*(*a*))
    *
    * The effect of *p* happens; *c* is passed along unchanged.
    */
  open class ProductStrength(tracked override val profunctor: Kleisli.Of[Monad.On[Total.type]])
      extends Bistrong(profunctor, Total.Products) {
    import profunctor.monad.M

    def left[A: Type, B: Type, C: Type]: (A -> M[B]) -> ((C, A)) -> M[(C, B)] = {
      p => (c, a) => profunctor.monad.map[B, (C, B)](b => (c, b))(p(a))
    }
  }

  /** Every Kleisli promonad of a monad on a category with coproducts is strong for coproducts, where
    *   - *τ*(*p*) = [*η* ∘ *ι*₁,*M*(*ι*₂) ∘ *p*]
    *
    * On the left the value passes through without effect; on the right the arrow runs.
    */
  open class CoproductStrength(
    tracked override val profunctor: Kleisli,
    tracked override val monoidal: Cocartesian.On[profunctor.domain.type],
  ) extends Bistrong(profunctor, monoidal) {
    import profunctor.monad.M
    import profunctor.monad.category.{Obj, -->, >>>}
    import monoidal.+

    private given SumIsObj: [A: Obj, B: Obj] => ((A + B) is Obj) = monoidal.tensor.objects[A, B]

    private given MIsObj: [A: Obj] => (M[A] is Obj) = profunctor.monad.objects[A]

    def left[A: Obj, B: Obj, C: Obj]: (A --> M[B]) -> ((C + A) --> M[C + B]) = {
      p =>
        monoidal.copair(
          monoidal.inl[C, B] >>> profunctor.monad.unit[C + B],
          p >>> profunctor.monad.map(monoidal.inr[C, B]),
        )
    }
  }

  /** The initial object of the arrows of a Kleisli promonad over a category with an initial object 0, where
    *   - ¡ = *η* ∘ ¡: the unique arrow out of 0 is pure
    */
  open class InitialOf(tracked val promonad: Kleisli, tracked val initial: Initial.Of[promonad.category.type])
      extends Initial(promonad.arrows) {
    import promonad.category.Obj

    type Self = initial.I

    private given IIsObj: (initial.I is Obj) = initial.evidence

    def evidence: initial.I is Obj = {
      initial.evidence
    }

    def absurd[A: Obj]: promonad.P[initial.I, A] = {
      promonad.unit(initial.absurd[A])
    }
  }

  /** The coproduct of two objects in the arrows of a Kleisli promonad, from their coproduct *S* in its category,
    * where
    *   - the injections are the pure arrows *η* ∘ *ι*₁ and *η* ∘ *ι*₂
    *   - the copairing of *f*: *A*₁ → *M*[*X*] and *g*: *A*₂ → *M*[*X*] is their copairing [*f*,*g*] at *M*[*X*]: it runs
    *     the arrow of the side it is given
    */
  final class CoproductOf(tracked val promonad: Kleisli, tracked val coproduct: Coproduct.Of[promonad.category.type])
      extends Coproduct(
        promonad.arrows,
        promonad.arrows.Object[coproduct.A1](using coproduct.left.evidence),
        promonad.arrows.Object[coproduct.A2](using coproduct.right.evidence),
      ) {
    import promonad.category.Obj
    import promonad.P

    type Self = coproduct.S

    private given A1IsObj: (coproduct.A1 is Obj) = coproduct.left.evidence
    private given A2IsObj: (coproduct.A2 is Obj) = coproduct.right.evidence
    private given SIsObj: (coproduct.S is Obj)   = coproduct.evidence

    def evidence: coproduct.S is Obj = {
      coproduct.evidence
    }

    def inl: P[coproduct.A1, coproduct.S] = {
      promonad.unit(coproduct.inl)
    }

    def inr: P[coproduct.A2, coproduct.S] = {
      promonad.unit(coproduct.inr)
    }

    def copair[X: Obj](f: P[coproduct.A1, X], g: P[coproduct.A2, X]): P[coproduct.S, X] = {
      coproduct.copair[promonad.monad.M[X]](f, g)(using promonad.monad.objects[X])
    }
  }

  /** The binary coproducts of the arrows of a Kleisli promonad over a category with binary coproducts: the coproducts
    * of its category, each as a [[CoproductOf]].
    */
  open class CoproductsOf(
    tracked val promonad: Kleisli,
    tracked val coproducts: Coproducts.On[promonad.category.type],
  ) extends Coproducts(promonad.arrows) {
    import category.Object
    import promonad.category.Obj

    type Self = coproducts.F

    def objects[A: Obj, B: Obj]: coproducts.F[A, B] is Obj = {
      coproducts.objects[A, B]
    }

    def coproduct[X: Obj, Y: Obj]
      : F[X, Y] is Coproduct.Of[category.type] { val left: X is Object; val right: Y is Object } = {
      CoproductOf(promonad, coproducts.coproduct[X, Y])
    }
  }

  /** The cocartesian structure of the arrows of a Kleisli promonad over a cocartesian category, where
    *   - the initial object and the coproducts are those of the category, with pure injections
    *   - [*f*,*g*] runs the arrow of the side it is given
    *
    * So the Kleisli category of a monad has the coproducts of its base, and its Freyd category over coproducts is
    * monoidal: of two arrows side by side only one runs, and interchange holds.
    */
  open class CocartesianOf(
    tracked val promonad: Kleisli,
    tracked val coproducts: Cocartesian.On[promonad.category.type],
  ) extends Cocartesian(
        promonad.arrows,
        InitialOf(promonad, coproducts.unit),
        CoproductsOf(promonad, coproducts.tensor),
      ) {
    import promonad.category.Obj
    import promonad.P

    /** Laws of the cocartesian structure of Kleisli arrows, besides those of [[Cocartesian]]. */
    object CocartesianOfLaws {

      /** *τ*(*p*) = *C* + *p*
        *
        * The strength over coproducts ([[CoproductStrength]]) is the coproduct of arrows, so the tensor of the Freyd
        * category over coproducts is a bifunctor.
        */
      def strengthIsCoproduct[A: Obj, B: Obj, C: Obj](p: P[A, B])(using P[C + A, C + B] is Observable): Boolean = {
        CoproductStrength(promonad, coproducts).left[A, B, C](p) =?= tensor.rmap[A, B, C](p)
      }
    }
  }

  /** The restriction structure on the arrows of a Kleisli promonad over a restriction monad, where
    *   - *p̄*(*a*) = *M*(*x* ↦ *a*)(*p*(*a*)‾): run the test of *p*, then return the input
    */
  open class RestrictionOf(
    tracked val promonad: Kleisli.Of[Monad.On[Total.type]],
    tracked val restriction: Monad.Restriction.On[promonad.monad.type],
  ) extends Restriction(promonad.arrows) {
    import promonad.monad.M

    def restrict[A: Type, B: Type](p: A -> M[B]): A -> M[A] = {
      a => promonad.monad.map[Unit, A](_ => a)(restriction.restrict(p(a)))
    }
  }

  /** The classical structure on the arrows of a Kleisli promonad over a classical monad, where
    *   - 0 = *a* ↦ 0′, *p̄*ᶜ(*a*) = *M*(*x* ↦ *a*)(*p*(*a*)‾ᶜ′) and (*p* ⊳ *q*)(*a*) = *p*(*a*) ⊳′ *q*(*a*)
    */
  open class ClassicalOf(
    tracked val promonad: Kleisli.Of[Monad.On[Total.type]],
    tracked val classical: Monad.Classical.On[promonad.monad.type],
  ) extends Classical(promonad.arrows) {
    import promonad.monad.M

    def restrict[A: Type, B: Type](p: A -> M[B]): A -> M[A] = {
      a => promonad.monad.map[Unit, A](_ => a)(classical.restrict(p(a)))
    }

    def zero[A: Type, B: Type]: A -> M[B] = {
      _ => classical.zero[B]
    }

    def complement[A: Type, B: Type](p: A -> M[B]): A -> M[A] = {
      a => promonad.monad.map[Unit, A](_ => a)(classical.complement(p(a)))
    }

    def orElse[A: Type, B: Type](p: A -> M[B], q: A -> M[B]): A -> M[B] = {
      a => classical.orElse(p(a), q(a))
    }

    /** Laws of the classical monad that its Kleisli arrows state, besides those of [[Classical]]. */
    object ClassicalOfLaws {

      /** *attempt*(*p*(*a*)) = *M*(*Some*)(*p*(*a*)) ⊳′ *η*(*None*)
        */
      def attemptDefinition[A: Type, B: Type](p: A -> M[B])(using (A -> M[Option[B]]) is Observable): Boolean = {
        val attempted: A -> M[Option[B]] = a => classical.attempt(p(a))
        val defined: A -> M[Option[B]]   = { a =>
          classical.orElse(promonad.monad.map[B, Option[B]](b => Some(b))(p(a)), promonad.monad.unit[Option[B]](None))
        }
        attempted =?= defined
      }
    }
  }

  /** The guarded iteration of a Kleisli promonad over a monad with guarded iteration: *p*† = *p*†′. */
  open class GuardedIterationOf(
    tracked override val strong: Bistrong.On[Kleisli.Of[Monad.On[Total.type]]] {
      val monoidal: Total.Coproducts.type
    },
    tracked val iteration: Monad.GuardedIteration.On[strong.profunctor.monad.type],
  ) extends GuardedIteration(strong) {
    import strong.profunctor.monad.M

    def iterate[A: Type, X: Type](p: X -> M[Either[A, X]]): X -> M[A] = {
      iteration.iterate(p)
    }
  }

  /** The Kleisli exponentials of a Kleisli promonad over a monad *M* on 𝒮, where
    *   - *A* ⇒ *B* = *A* → *M*[*B*]
    *   - *ev*(*p*,*a*) = *p*(*a*)
    *   - Λ(*p*) = *x* ↦ *a* ↦ *p*(*x*,*a*)
    */
  open class ClosedFreydOf(tracked override val strong: ProductStrength) extends ClosedFreyd(strong) {
    import strong.profunctor.monad.M

    type Exp[A, B] = A -> M[B]

    def objects[A: Type, B: Type]: (A -> M[B]) is Type = {
      Type.TIsType
    }

    def eval[A: Type, B: Type]: ((A -> M[B], A)) -> M[B] = {
      (p, a) => p(a)
    }

    def curry[A: Type, B: Type, X: Type](p: ((X, A)) -> M[B]): X -> A -> M[B] = {
      x => a => p((x, a))
    }
  }

  /** The Kleisli promonad of `Option` on 𝒮: functions that may fail. */
  object OptionKleisli extends Kleisli(Monad.OptionIsMonad)

  /** Functions that may fail, run side by side on pairs. */
  object OptionProduct extends ProductStrength(OptionKleisli)

  /** Functions that may fail, run on one side of a tagged union. */
  object OptionCoproduct extends CoproductStrength(OptionKleisli, Total.Coproducts)

  /** Functions that may fail have the coproducts of 𝒮: tagged unions. */
  object OptionCoproducts extends CocartesianOf(OptionKleisli, Total.Coproducts)

  /** Functions that may fail: a classical restriction category, with failure as zero and ordered choice as override. */
  object OptionDomains extends ClassicalOf(OptionKleisli, Monad.Classical.OptionIsClassical)
}
