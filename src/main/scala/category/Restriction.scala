package parrot
package category

import scala.annotation.targetName

/** A restriction promonad on an underlying category **C**.
  *
  * Represents a promonad *P* whose induced category is a Cockett–Lack restriction category, where every morphism *p*:
  * *A* ~> *B* has a restriction idempotent *p̄*: *A* ~> *A* representing the partial identity on the domain of
  * definition of *p*.
  *
  * A morphism *p* is *total* if *p̄* = *id*.
  */
trait Restriction {
  type Self[_, _]: Promonad as RestrictionPromonad

  val SelfIsPromonad: Self is Promonad = RestrictionPromonad

  import SelfIsPromonad.*

  /** Maps a morphism *p*: *A* ~> *B* to its restriction idempotent *p̄*: *A* ~> *A*, the partial identity on the domain
    * of definition of *p*.
    */
  def restrict[A, B](p: A ~> B): A ~> A

  extension [A, B](p: A ~> B)
    /** Postfix extension for [[restrict]]. */
    @targetName("restrictExt")
    def restrict(using DummyImplicit): A ~> A = {
      Restriction.this.restrict(p)
    }

  /** Laws that any `Restriction` promonad must satisfy (the four Cockett–Lack restriction axioms). */
  object RestrictionLaws {

    /** **[R1]** *p* ∘ *p̄* = *p*
      */
    def restrictionIdentity[A, B](p: A ~> B)(using A ~> B is Eq): Boolean = {
      (p.restrict >>> p) === p
    }

    /** **[R2]** *p̄* ∘ *q̄* = *q̄* ∘ *p̄*
      */
    def restrictionCommutativity[A, B, C](p: A ~> B, q: A ~> C)(using A ~> A is Eq): Boolean = {
      (p.restrict >>> q.restrict) === (q.restrict >>> p.restrict)
    }

    /** **[R3]** (*q* ∘ *p̄*)̄ = *q̄* ∘ *p̄*
      */
    def restrictionCompose[A, B, C](p: A ~> B, q: A ~> C)(using A ~> A is Eq): Boolean = {
      (p.restrict >>> q).restrict === (p.restrict >>> q.restrict)
    }

    /** **[R4]** *q̄* ∘ *p* = *p* ∘ (*q* ∘ *p*)̄
      */
    def restrictionPrecompose[A, B, C](p: A ~> B, q: B ~> C)(using A ~> B is Eq): Boolean = {
      (p >>> q.restrict) === ((p >>> q).restrict >>> p)
    }
  }
}

object Restriction {

  /** Summons the `Restriction` instance of `P`. */
  def apply[P[_, _]: Restriction]: P is Restriction = summon

  /** `Function` is a `Restriction` on the category of partial functions **pType**, where the restriction of a partial
    * function is the partial identity on its domain of definition.
    */
  given FunctionIsRestriction: Function is Restriction {
    override given RestrictionPromonad: Promonad.FunctionIsPromonad.type = Promonad.FunctionIsPromonad
    override val SelfIsPromonad: Promonad.FunctionIsPromonad.type        = Promonad.FunctionIsPromonad

    def restrict[A, B](p: A => B): A => A = {
      a =>
        {
          val _ = p(a)
          a
        }
    }
  }
}
