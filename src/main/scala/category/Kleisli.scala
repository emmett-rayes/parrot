package parrot
package category

/** The Kleisli promonad of a monad *M* on **K**: effectful arrows *A* → *M*[*B*].
  *
  * Represents a promonad over **K**, where
  *   - *P*(*A*,*B*) = **K**(*A*,*M*[*B*])
  *   - *unit*(*f*) = *η* ∘ *f* embeds the pure morphisms
  *   - *multiply*(*g*,*f*) = *g*\* ∘ *f* runs *f*, then *g* on its result
  */
open class Kleisli(tracked val M: Monad) extends Promonad(M.K) {
  import M.K.{Obj, -->, >>>}

  type Self[A, B] = A --> M.M[B]

  private given MIsObj: [A: Obj] => (M.M[A] is Obj) = M.objects[A]

  def unit[A: Obj, B: Obj](f: A --> B): A --> M.M[B] = {
    f >>> M.unit[B]
  }

  def multiply[A: Obj, B: Obj, C: Obj](g: B --> M.M[C], f: A --> M.M[B]): A --> M.M[C] = {
    f >>> M.bind(g)
  }
}

object Kleisli {

  /** Every Kleisli promonad of a monad on 𝒮 is strong for products, where
    *   - *first*(*p*) = (*a*,*c*) ↦ *M*(*b* ↦ (*b*,*c*))(*p*(*a*))
    *
    * The effect of *p* happens; *c* is passed along unchanged.
    */
  open class ProductStrength(tracked override val P: Kleisli { val M: Monad.On[Total.type] })
      extends Strong(P, Total.Product) {
    def first[A: Type, B: Type, C: Type](p: A -> P.M.M[B]): ((A, C)) -> P.M.M[(B, C)] = {
      (a, c) => P.M.map[B, (B, C)](b => (b, c))(p(a))
    }
  }

  /** Every Kleisli promonad of a monad on 𝒮 is strong for coproducts, where
    *   - *first*(*p*) = [*M*(*ι*₁) ∘ *p*,*η* ∘ *ι*₂]
    *
    * On the left the arrow runs; on the right the value passes through without effect.
    */
  open class CoproductStrength(tracked override val P: Kleisli { val M: Monad.On[Total.type] })
      extends Strong(P, Total.Coproduct) {
    def first[A: Type, B: Type, C: Type](p: A -> P.M.M[B]): Either[A, C] -> P.M.M[Either[B, C]] = {
      case Left(a)  => P.M.map[B, Either[B, C]](b => Left(b))(p(a))
      case Right(c) => P.M.unit[Either[B, C]](Right(c))
    }
  }

  /** The restriction structure of a Kleisli promonad over a restriction monad, where
    *   - *p̄*(*a*) = *M*(_ ↦ *a*)(*p*(*a*)‾): run the test of *p*, then return the input
    */
  open class RestrictionOf(
    tracked override val P: Kleisli { val M: Monad.On[Total.type] },
    tracked val R: RestrictionMonad { val M: P.M.type },
  ) extends Restriction(P) {

    def restrict[A: Type, B: Type](p: A -> P.M.M[B]): A -> P.M.M[A] = {
      a => P.M.map[Unit, A](_ => a)(R.restrict(p(a)))
    }
  }

  /** The classical structure of a Kleisli promonad over a classical monad, where
    *   - 0 = _ ↦ 0′, *p̄*ᶜ(*a*) = *M*(_ ↦ *a*)(*p*(*a*)‾ᶜ′) and (*p* ⊳ *q*)(*a*) = *p*(*a*) ⊳′ *q*(*a*)
    *   - *attempt*(*p*)(*a*) tags the result of *p*(*a*), or returns *a* on the right where *p*(*a*) fails
    */
  open class ClassicalOf(
    tracked override val P: Kleisli { val M: Monad.On[Total.type] },
    tracked val R: ClassicalMonad { val M: P.M.type },
  ) extends Classical(P, Total.Coproduct) {

    def restrict[A: Type, B: Type](p: A -> P.M.M[B]): A -> P.M.M[A] = {
      a => P.M.map[Unit, A](_ => a)(R.restrict(p(a)))
    }

    def zero[A: Type, B: Type]: A -> P.M.M[B] = {
      _ => R.zero[B]
    }

    def complement[A: Type, B: Type](p: A -> P.M.M[B]): A -> P.M.M[A] = {
      a => P.M.map[Unit, A](_ => a)(R.complement(p(a)))
    }

    def orElse[A: Type, B: Type](p: A -> P.M.M[B], q: A -> P.M.M[B]): A -> P.M.M[B] = {
      a => R.orElse(p(a), q(a))
    }

    override def attempt[A: Type, B: Type](p: A -> P.M.M[B]): A -> P.M.M[Either[B, A]] = {
      a =>
        P.M.map[Option[B], Either[B, A]] {
          case Some(b) => Left(b)
          case None    => Right(a)
        }(R.attempt(p(a)))
    }
  }

  /** The iteration of a Kleisli promonad over an Elgot monad: *p*† = *p*†′. */
  open class ElgotOf(
    tracked override val S: Strong {
      val P: Kleisli { val M: Monad.On[Total.type] }; val M: Total.Coproduct.type
    },
    tracked val E: ElgotMonad { val M: S.P.M.type },
  ) extends Elgot(S) {

    def iterate[A: Type, X: Type](p: X -> S.P.M.M[Either[A, X]]): X -> S.P.M.M[A] = {
      E.iterate(p)
    }
  }

  /** The Kleisli promonad of `Option` on 𝒮: functions that may fail. */
  object OptionKleisli extends Kleisli(Monad.OptionIsMonad)

  /** Functions that may fail, run side by side on pairs. */
  object OptionProduct extends ProductStrength(OptionKleisli)

  /** Functions that may fail, run on one side of a tagged union. */
  object OptionCoproduct extends CoproductStrength(OptionKleisli)

  /** Functions that may fail: a classical restriction category, with failure as zero and ordered choice as override. */
  object OptionDomains extends ClassicalOf(OptionKleisli, ClassicalMonad.OptionIsClassical)
}
