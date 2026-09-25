package parrot
package category

import scala.annotation.targetName

/** A profunctor on an underlying category **C**.
  *
  * Represents a functor *P*: **C**^*op* × **C** → **Type**, where
  *   - *P*[*A*,*B*] is the object part, contravariant in *A* and covariant in *B*
  *   - *P*(*f*,*g*) is the morphism part
  */
trait Profunctor {
  type Self[_, _]
  final type ~> = Self

  /** The promonad inducing the underlying category **C**. */
  type On[_, _]: Promonad
  final type ==> = On

  /** Maps a pair of morphisms *f*: *C* ==> *A*, *g*: *B* ==> *D* to a morphism *P*[*A*,*B*] → *P*[*C*,*D*]. */
  def dimap[A, B, C, D](f: C ==> A, g: B ==> D)(p: A ~> B): C ~> D

  /** Maps a morphism *f*: *C* ==> *A* to a morphism *P*[*A*,*B*] → *P*[*C*,*B*]. */
  def lmap[A, B, C](f: C ==> A)(p: A ~> B): C ~> B = {
    dimap(f, Promonad[On].identity)(p)
  }

  /** Maps a morphism *g*: *B* ==> *D* to a morphism *P*[*A*,*B*] → *P*[*A*,*D*]. */
  def rmap[A, B, D](g: B ==> D)(p: A ~> B): A ~> D = {
    dimap(Promonad[On].identity, g)(p)
  }

  extension [A, B](p: A ~> B)
    /** Infix extension for [[dimap]]. */
    @targetName("dimapExt")
    def dimap[C, D](f: C ==> A, g: B ==> D): C ~> D = {
      Profunctor.this.dimap(f, g)(p)
    }

  extension [A, B](p: A ~> B)
    /** Infix extension for [[lmap]]. */
    @targetName("lmapExt")
    def lmap[C](f: C ==> A): C ~> B = {
      Profunctor.this.lmap(f)(p)
    }

  extension [A, B](p: A ~> B)
    /** Infix extension for [[rmap]]. */
    @targetName("rmapExt")
    def rmap[D](g: B ==> D): A ~> D = {
      Profunctor.this.rmap(g)(p)
    }

  /** Laws that any `Profunctor` must satisfy. */
  object ProfunctorLaws {

    /** *P*(*id*,*id*) = *id*
      */
    def identity[A, B](p: A ~> B)(using A ~> B is Eq): Boolean = {
      p.dimap(Promonad[On].identity, Promonad[On].identity) === p
    }

    /** *P*(*f1*,*g1*) ∘ *P*(*f2*,*g2*) = *P*(*f2* ∘ *f1*,*g1* ∘ *g2*)
      */
    def composition[A, B, C, D, E, F](
      p: A ~> B,
      f1: C ==> A,
      g1: B ==> D,
      f2: E ==> C,
      g2: D ==> F,
    )(using E ~> F is Eq): Boolean = {
      p.dimap(f1, g1).dimap(f2, g2) === p.dimap(f2 andThen f1, g1 andThen g2)
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

    def dimap[A, B, C, D](f: C =:= A, g: B =:= D)(p: A =:= B): C =:= D = {
      f andThen p andThen g
    }
  }

  /** `Profunctor` instance for `Function` on the category **Type**. */
  given FunctionIsProfunctor: Function is Profunctor {
    type On = Function

    def dimap[A, B, C, D](f: C => A, g: B => D)(p: A => B): C => D = {
      f andThen p andThen g
    }
  }
}
