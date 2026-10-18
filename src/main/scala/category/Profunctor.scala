package parrot
package category

import scala.annotation.targetName

/** A profunctor on an underlying category **C**.
  *
  * Represents an endobifunctor *P*: **C**^op × **C** → **Type**, where
  *   - *P*[*A*,*B*] is the object part, contravariant in *A* and covariant in *B*
  *   - *P*(*f*,*g*) is the morphism part
  */
trait Profunctor {
  type Self[_, _]
  final type ~> = Self

  /** The promonad inducing the underlying category **C**. */
  type On[_, _]: Promonad as ProfunctorOnPromonad
  final type --> = On

  val OnIsPromonad: On is Promonad = ProfunctorOnPromonad

  import OnIsPromonad.*

  /** Maps a pair of morphisms *f*: *C* --> *A* and *g*: *B* --> *D* to a morphism *P*[*A*,*B*] → *P*[*C*,*D*]. */
  def dimap[A, B, C, D](f: C --> A, g: B --> D)(p: A ~> B): C ~> D

  /** Maps a morphism *f*: *C* --> *A* to a morphism *P*[*A*,*B*] → *P*[*C*,*B*]. */
  def lmap[A, B, C](f: C --> A)(p: A ~> B): C ~> B = {
    dimap(f, identity)(p)
  }

  /** Maps a morphism *g*: *B* --> *D* to a morphism *P*[*A*,*B*] → *P*[*A*,*D*]. */
  def rmap[A, B, D](g: B --> D)(p: A ~> B): A ~> D = {
    dimap(identity, g)(p)
  }

  extension [A, B](p: A ~> B)
    /** Infix extension for [[dimap]]. */
    @targetName("dimapExt")
    def dimap[C, D](f: C --> A, g: B --> D): C ~> D = {
      Profunctor.this.dimap(f, g)(p)
    }

  extension [A, B](p: A ~> B)
    /** Infix extension for [[lmap]]. */
    @targetName("lmapExt")
    def lmap[C](f: C --> A): C ~> B = {
      Profunctor.this.lmap(f)(p)
    }

  extension [A, B](p: A ~> B)
    /** Infix extension for [[rmap]]. */
    @targetName("rmapExt")
    def rmap[D](g: B --> D): A ~> D = {
      Profunctor.this.rmap(g)(p)
    }

  /** Laws that any `Profunctor` must satisfy. */
  object ProfunctorLaws {

    /** *P*(*id*,*id*) = *id*
      */
    def identity[A, B](using ((A ~> B) => (A ~> B)) is Eq): Boolean = {
      dimap(OnIsPromonad.identity[A], OnIsPromonad.identity[B]) === scala.Predef.identity[A ~> B]
    }

    /** *P*(*f*₁ ∘ *f*₂,*g*₂ ∘ *g*₁) = *P*(*f*₂,*g*₂) ∘ *P*(*f*₁,*g*₁)
      */
    def composition[A, B, C, D, E, F](
      f1: C --> A,
      g1: B --> D,
      f2: E --> C,
      g2: D --> F,
    )(using ((A ~> B) => (E ~> F)) is Eq): Boolean = {
      dimap(f2 andThen f1, g1 andThen g2) === dimap(f1, g1).andThen(dimap(f2, g2))
    }
  }
}

object Profunctor {

  /** Refines the `On` type of `Profunctor` to `T`. */
  infix type on[P <: Profunctor, T[_, _]] = P { type On = T }

  /** Summons the `Profunctor` instance of `P`. */
  def apply[P[_, _]: Profunctor]: P is Profunctor = summon

  /** `Profunctor` instance for `=:=` on the discrete category *Ob*(**Type**). */
  given TypeEqIsProfunctor: =:= is Profunctor {
    type On = =:=

    override given ProfunctorOnPromonad: Promonad.TypeEqIsPromonad.type = Promonad.TypeEqIsPromonad
    override val OnIsPromonad: Promonad.TypeEqIsPromonad.type           = Promonad.TypeEqIsPromonad

    def dimap[A, B, C, D](f: C =:= A, g: B =:= D)(p: A =:= B): C =:= D = {
      g.substituteCo(p.substituteCo(f))
    }
  }

  /** `Profunctor` instance for `Function` on the category **Type**. */
  given FunctionIsProfunctor: Function is Profunctor {
    type On = PureFunction

    override given ProfunctorOnPromonad: PureFunction.PureFunctionIsPromonad.type = PureFunction.PureFunctionIsPromonad
    override val OnIsPromonad: PureFunction.PureFunctionIsPromonad.type           = PureFunction.PureFunctionIsPromonad

    def dimap[A, B, C, D](f: C -> A, g: B -> D)(p: A => B): C => D = {
      f.andThen(p.andThen(g))
    }
  }
}
