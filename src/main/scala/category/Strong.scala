package parrot
package category

import scala.annotation.targetName

/** A strong profunctor on an underlying monoidal category **C**.
  *
  * Represents a profunctor *P*: **C**^*op* × **C** → **Type** equipped with a tensorial strength with respect to a
  * monoidal category (**C**, ⊗, *I*), where
  *   - *first*: *P*[*A*, *B*] → *P*[*A* ⊗ *C*, *B* ⊗ *C*] is the left strength
  *   - *second*: *P*[*A*, *B*] → *P*[*C* ⊗ *A*, *C* ⊗ *B*] is the right strength
  */
trait Strong extends Profunctor {
  type Self[_, _]

  override type On[_, _]: Monoidal

  val Mon: On is Monoidal = summon
  import Mon.*

  /** Strong tensorial action on the left: *P*[*A*, *B*] → *P*[*A* ⊗ *C*, *B* ⊗ *C*]. */
  def first[A, B, C](p: A ~> B): (A * C) ~> (B * C)

  /** Strong tensorial action on the right: *P*[*A*, *B*] → *P*[*C* ⊗ *A*, *C* ⊗ *B*]. */
  def second[A, B, C](p: A ~> B): (C * A) ~> (C * B)

  extension [A, B](p: A ~> B)
    /** Infix extension for [[first]]. */
    @targetName("firstExt")
    def first[C]: (A * C) ~> (B * C) = {
      Strong.this.first(p)
    }

  extension [A, B](p: A ~> B)
    /** Infix extension for [[second]]. */
    @targetName("secondExt")
    def second[C]: (C * A) ~> (C * B) = {
      Strong.this.second(p)
    }

  /** Laws that any `Strong` profunctor must satisfy. */
  object StrongLaws {

    /** *first*(*P*(*f*, *g*)(*p*)) = *P*(*f* ⊗ *id*, *g* ⊗ *id*)(*first*(*p*))
      */
    def firstNaturality[A, B, C, D, X](p: A ~> B, f: C ==> A, g: B ==> D)(
      using (C * X) ~> (D * X) is Eq
    ): Boolean = {
      p.dimap(f, g).first[X] === p.first[X].dimap(f *** Promonad[On].identity[X], g *** Promonad[On].identity[X])
    }

    /** *second*(*P*(*f*, *g*)(*p*)) = *P*(*id* ⊗ *f*, *id* ⊗ *g*)(*second*(*p*))
      */
    def secondNaturality[A, B, C, D, X](p: A ~> B, f: C ==> A, g: B ==> D)(
      using (X * C) ~> (X * D) is Eq
    ): Boolean = {
      p.dimap(f, g).second[X] === p.second[X].dimap(Promonad[On].identity[X] *** f, Promonad[On].identity[X] *** g)
    }

    /** *P*(*ρ*⁻¹, *ρ*)(*first*(*p*)) = *p*
      */
    def firstUnitality[A, B](p: A ~> B)(
      using A ~> B is Eq
    ): Boolean = {
      p.first[I].dimap(rightUnitorInv[A], rightUnitor[B]) === p
    }

    /** *P*(*λ*⁻¹, *λ*)(*second*(*p*)) = *p*
      */
    def secondUnitality[A, B](p: A ~> B)(
      using A ~> B is Eq
    ): Boolean = {
      p.second[I].dimap(leftUnitorInv[A], leftUnitor[B]) === p
    }

    /** *P*(*α*, *α*⁻¹)(*first*(*p*)) = *first*(*first*(*p*))
      */
    def firstAssociativity[A, B, C, D](p: A ~> B)(
      using ((A * C) * D) ~> ((B * C) * D) is Eq
    ): Boolean = {
      p.first[C * D].dimap(associate[A, C, D], unassociate[B, C, D]) === p.first[C].first[D]
    }

    /** *P*(*α*⁻¹, *α*)(*second*(*p*)) = *second*(*second*(*p*))
      */
    def secondAssociativity[A, B, C, D](p: A ~> B)(
      using (D * (C * A)) ~> (D * (C * B)) is Eq
    ): Boolean = {
      p.second[D * C].dimap(unassociate[D, C, A], associate[D, C, B]) === p.second[C].second[D]
    }
  }
}

object Strong {
  import Profunctor.on

  /** Summons the `Strong` instance of `P`. */
  def apply[P[_, _]: Strong]: P is Strong = summon

  /** `Function` is canonically `Strong` over itself under its cartesian monoidal structure. */
  given FunctionIsStrong: (F: Function is Profunctor on Function) => Function is Strong {
    export F.{Self as _, *}

    override val Mon: Function is Monoidal.`with`[Unit, Tuple2] = summon

    def first[A, B, C](p: A => B): ((A, C)) => (B, C) = {
      (a, c) => (p(a), c)
    }

    def second[A, B, C](p: A => B): ((C, A)) => (C, B) = {
      (c, a) => (c, p(a))
    }
  }
}
