package parrot
package category

import scala.annotation.targetName

/** A promonad on an underlying category **C**.
  *
  * Represents a monoid *P* in the monoidal category of endoprofunctors **Prof** on **C**, where
  *   - *P* ⇒ *Q* are morphisms of **Prof** (natural transformations between profunctors)
  *   - *Hom* is the unit object of **Prof** (the Hom-profunctor)
  *   - ⋄ is the tensor product of **Prof**
  *   - *η*: *Hom* ⇒ *P* is the unit of the monoid
  *   - *μ*: *P* ⋄ *P* ⇒ *P* is the multiplication of the monoid
  *
  * Every promonad on **C** induces a category with objects *Ob*(**C**) and hom-sets *P*[*A*,*B*], where
  *   - *id* : *A* ~> *A* are the identity morphisms given by the unit *η*
  *   - ∘ is the composition given by the multiplication *μ*
  */
trait Promonad extends Profunctor {
  type Self[_, _]

  /** The unit natural transformation *η*: *Hom* ⇒ *P*.
    *
    * Maps a morphism *f*: *A* ==> *B* to an element *η*(*f*) in *A* ~> *B*.
    */
  def unit[A, B](f: A ==> B): A ~> B

  /** The multiplication natural transformation *μ*: *P* ⋄ *P* ⇒ *P*.
    *
    * Maps two elements *q* in *B* ~> *C* and *p* in *A* ~> *B* to an element *μ*(*q*,*p*) in *A* ~> *C*.
    */
  def multiply[A, B, C](q: B ~> C, p: A ~> B): A ~> C

  /** The identity morphism *id* = *η*(*id*) in *A* ~> *A* of the category induced by *P*. */
  def identity[A]: A ~> A = {
    unit(Promonad[On].identity)
  }

  /** Composes two morphisms *p*: *B* ~> *C* and *q*: *A* ~> *B* to a morphism *p* ∘ *q*: *A* ~> *C* in the category
    * induced by *P*.
    */
  def compose[A, B, C](p: B ~> C, q: A ~> B): A ~> C = {
    multiply(p, q)
  }

  /** Composes two morphisms *p*: *A* ~> *B* and *q*: *B* ~> *C* to a morphism *q* ∘ *p* (or *p* ⨾ *q*): *A* ~> *C* in
    * the category induced by *P*.
    */
  def andThen[A, B, C](p: A ~> B, q: B ~> C): A ~> C = {
    multiply(q, p)
  }

  override def dimap[A, B, C, D](f: C ==> A, g: B ==> D)(p: A ~> B): C ~> D = {
    unit(f) >>> p >>> unit(g)
  }

  extension [B, C](p: B ~> C)
    /** Infix extension for [[compose]]. */
    @targetName("composeExt")
    infix def compose[A](q: A ~> B): A ~> C = {
      Promonad.this.compose(p, q)
    }

  extension [A, B](p: A ~> B)
    /** Infix extension for [[andThen]]. */
    @targetName("andThenExt")
    infix def andThen[C](q: B ~> C): A ~> C = {
      Promonad.this.andThen(p, q)
    }

  extension [B, C](p: B ~> C)
    /** Alias for [[compose]]. */
    def <<<[A](q: A ~> B): A ~> C = {
      p compose q
    }

  extension [A, B](p: A ~> B)
    /** Alias for [[andThen]]. */
    def >>>[C](q: B ~> C): A ~> C = {
      p andThen q
    }

  /** Laws that any `Promonad` must satisfy. */
  object PromonadLaws {

    /** *P*(*h*,*k*) ∘ *η* = *η* ∘ *Hom*(*h*,*k*)
      *
      * *P*(*h*,*k*)(*η*(*f*)) = *η*(*Hom*(*h*,*k*)(*f*))
      */
    def unitNaturality[A, B, C, D](
      f: A ==> B,
      h: C ==> A,
      k: B ==> D,
    )(using C ~> D is Eq): Boolean = {
      unit(f).dimap(h, k) === unit(h >>> f >>> k)
    }

    /** *P*(*h*,*k*) ∘ *μ* = *μ* ∘ (*P* ⋄ *P*)(*h*,*k*)
      *
      * *P*(*h*,*k*)(*μ*(*q*,*p*)) = *μ*(*P*(*id*,*k*)(*q*),*P*(*h*,*id*)(*p*))
      */
    def multiplicationNaturality[A, B, C, D, E](
      p: A ~> B,
      q: B ~> C,
      h: D ==> A,
      k: C ==> E,
    )(using D ~> E is Eq): Boolean = {
      multiply(q, p).dimap(h, k) === multiply(q.rmap(k), p.lmap(h))
    }

    /** *id* ∘ *p* = *p*
      */
    def leftIdentity[A, B](p: A ~> B)(using A ~> B is Eq): Boolean = {
      (p >>> identity) === p
    }

    /** *p* ∘ *id* = *p*
      */
    def rightIdentity[A, B](p: A ~> B)(using A ~> B is Eq): Boolean = {
      (identity >>> p) === p
    }

    /** *r* ∘ (*q* ∘ *p*) = (*r* ∘ *q*) ∘ *p*
      */
    def associativity[A, B, C, D](
      p: A ~> B,
      q: B ~> C,
      r: C ~> D,
    )(using A ~> D is Eq): Boolean = {
      ((p >>> q) >>> r) === (p >>> (q >>> r))
    }
  }
}

object Promonad {

  /** Summons the `Promonad` instance of `P`. */
  def apply[P[_, _]: Promonad]: P is Promonad = summon

  /** `Promonad` instance for `=:=` on the discrete category *Ob*(**Type**). */
  given TypeEqIsPromonad: =:= is Promonad {
    export Profunctor.TypeEqIsProfunctor.On

    def unit[A, B](f: A =:= B): A =:= B = {
      f
    }

    def multiply[A, B, C](q: B =:= C, p: A =:= B): A =:= C = {
      q.substituteCo(p)
    }

    override def identity[A]: A =:= A = {
      summon[A =:= A]
    }
  }

  /** `Promonad` instance for `Function` on the category **Type**. */
  given FunctionIsPromonad: (P: Function is Profunctor on Function) => Function is Promonad {
    export P.{Self as _, dimap as _, *}

    def unit[A, B](f: A => B): A => B = {
      f
    }

    def multiply[A, B, C](q: B => C, p: A => B): A => C = {
      a => q(p(a))
    }

    override def identity[A]: A => A = {
      scala.Predef.identity
    }
  }
}
