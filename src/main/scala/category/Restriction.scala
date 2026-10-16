package parrot
package category

import scala.annotation.targetName

/** A restriction promonad on an underlying category **C**.
  *
  * Represents a promonad *P* whose induced category is a restriction category, where
  *   - ‾: *P*[*A*, *B*] → *P*[*A*, *A*] is the restriction operation
  *
  * A morphism *f*: *A* ~> *B* is total if *f̄* = *id*.
  */
trait Restriction {
  type Self[_, _]: Promonad as RestrictionPromonad

  val SelfIsPromonad: Self is Promonad = RestrictionPromonad
  import SelfIsPromonad.*

  /** Maps a morphism *p*: *A* ~> *B* to its restriction *p̄*: *A* ~> *A*. */
  def restrict[A, B](p: A ~> B): A ~> A

  extension [A, B](p: A ~> B)
    /** Infix extension for [[restrict]]. */
    @targetName("restrictExt")
    def restrict(using DummyImplicit): A ~> A = {
      Restriction.this.restrict(p)
    }

  /** Laws that any `Restriction` must satisfy. */
  object RestrictionLaws {

    /** (R1) *f* ∘ *f̄* = *f*
      */
    def restrictionIdentity[A, B](p: A ~> B)(using A ~> B is Eq): Boolean = {
      (p.restrict >>> p) === p
    }

    /** (R2) *ḡ* ∘ *f̄* = *f̄* ∘ *ḡ*
      */
    def restrictionCommutativity[A, B, C](p: A ~> B, q: A ~> C)(using A ~> A is Eq): Boolean = {
      (p.restrict >>> q.restrict) === (q.restrict >>> p.restrict)
    }

    /** (R3) ‾(*g* ∘ *f̄*) = *ḡ* ∘ *f̄*
      */
    def restrictionCompose[A, B, C](p: A ~> B, q: A ~> C)(using A ~> A is Eq): Boolean = {
      (p.restrict >>> q).restrict === (p.restrict >>> q.restrict)
    }

    /** (R4) *h̄* ∘ *f* = *f* ∘ ‾(*h* ∘ *f*)
      */
    def restrictionPrecompose[A, B, C](p: A ~> B, q: B ~> C)(using A ~> B is Eq): Boolean = {
      (p >>> q.restrict) === ((p >>> q).restrict >>> p)
    }
  }
}

object Restriction {

  /** Summons the `Restriction` instance of `P`. */
  def apply[P[_, _]: Restriction]: P is Restriction = summon

  /** `Function` is a trivial `Restriction` on the category **Type**, where every morphism is total. */
  given FunctionIsRestriction: Function is Restriction {
    override given RestrictionPromonad: Promonad.FunctionIsPromonad.type = Promonad.FunctionIsPromonad
    override val SelfIsPromonad: Promonad.FunctionIsPromonad.type        = Promonad.FunctionIsPromonad

    def restrict[A, B](p: A => B): A => A = {
      a => a
    }
  }

  /** `PartialFunction` is a `Restriction` on the category of partial functions, where the restriction of a partial
    * function is the partial identity on its domain of definition.
    */
  given PartialFunctionIsRestriction: PartialFunction is Restriction {
    override given RestrictionPromonad: Promonad.PartialFunctionIsPromonad.type = Promonad.PartialFunctionIsPromonad
    override val SelfIsPromonad: Promonad.PartialFunctionIsPromonad.type        = Promonad.PartialFunctionIsPromonad

    def restrict[A, B](p: PartialFunction[A, B]): PartialFunction[A, A] = {
      case a if p.isDefinedAt(a) => a
    }
  }
}
