package parrot
package category

import Category.Type

/** The Kleisli promonad of a monad *M* on **C**: effectful arrows *A* → *M*[*B*].
  *
  * Represents a promonad over **C**, where
  *   - *P*(*A*,*B*) = **C**(*A*,*M*[*B*])
  *   - *unit*(*f*) = *η* ∘ *f* embeds the pure morphisms
  *   - *multiply*(*g*,*f*) = *g*∘ *f* runs *f*, then *g* on its result
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
  }

  /** The iteration of a Kleisli promonad over an Elgot monad: *p*† = *p*†′. */
  open class ElgotOf(
    tracked override val strong: Bistrong.On[Kleisli.Of[Monad.On[Total.type]]] {
      val monoidal: Total.Coproducts.type
    },
    tracked val elgot: Monad.Elgot.On[strong.profunctor.monad.type],
  ) extends Elgot(strong) {
    import strong.profunctor.monad.M

    def iterate[A: Type, X: Type](p: X -> M[Either[A, X]]): X -> M[A] = {
      elgot.iterate(p)
    }
  }

  /** The Kleisli promonad of `Option` on 𝒮: functions that may fail. */
  object OptionKleisli extends Kleisli(Monad.OptionIsMonad)

  /** Functions that may fail, run side by side on pairs. */
  object OptionProduct extends ProductStrength(OptionKleisli)

  /** Functions that may fail, run on one side of a tagged union. */
  object OptionCoproduct extends CoproductStrength(OptionKleisli, Total.Coproducts)

  /** Functions that may fail: a classical restriction category, with failure as zero and ordered choice as override. */
  object OptionDomains extends ClassicalOf(OptionKleisli, Monad.Classical.OptionIsClassical)
}
