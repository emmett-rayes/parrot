package parrot
package category

import scala.annotation.targetName

/** A promonad on **K** valued in 𝒮: a monoid in the endoprofunctors on **K**, i.e. a category of arrows built on top
  * of **K**.
  *
  * Represents a profunctor *P*: **K**ᵒᵖ × **K** → 𝒮 with
  *   - *unit*: **K**(*A*,*B*) → *P*(*A*,*B*), which embeds the morphisms of **K**
  *   - *multiply*: *P*(*B*,*C*) × *P*(*A*,*B*) → *P*(*A*,*C*), which composes arrows
  *
  * The profunctor action is derived: *P*(*f*,*g*)(*p*) = *unit*(*g*) ∘ *p* ∘ *unit*(*f*). The arrows form a category,
  * [[category]], with the objects of **K**, and *unit* is an identity-on-objects functor from **K** into it. Kleisli
  * categories and reified arrows such as parsers are promonads.
  */
abstract class Promonad(tracked override val K: Category) extends Endoprofunctor(K, Total) {
  import K.{Obj, -->}
  import K.op.--> as ~~>

  /** *unit*: **K**(*A*,*B*) → *P*(*A*,*B*).
    */
  def unit[A: Obj, B: Obj](f: A --> B): P[A, B]

  /** *multiply*: *P*(*B*,*C*) × *P*(*A*,*B*) → *P*(*A*,*C*).
    */
  def multiply[A: Obj, B: Obj, C: Obj](g: P[B, C], f: P[A, B]): P[A, C]

  /** The identity arrow *unit*(*id*). */
  final def identity[A: Obj]: P[A, A] = {
    unit(K.identity[A])
  }

  /** Arrows are values of 𝒮, so every arrow type is an object of 𝒮. */
  final def objects[A: Obj, B: Obj]: P[A, B] is Type = {
    Type.TIsType
  }

  /** *P*(*f*,*g*)(*p*) = *unit*(*g*) ∘ *p* ∘ *unit*(*f*)
    */
  override def bimap[A1: Obj, B1: Obj, A2: Obj, B2: Obj](f: A1 ~~> A2, g: B1 --> B2): P[A1, B1] -> P[A2, B2] = {
    p => multiply(unit(g), multiply(p, unit[A2, A1](f)))
  }

  /** The category of arrows: the objects of **K**, morphisms *P*(*A*,*B*), identity and composition of *P*. */
  final lazy val category: Promonad.Underlying { val P: Promonad.this.type } = Promonad.Underlying(this)

  extension [A: Obj, B: Obj](p: P[A, B])
    /** Sequences arrows in diagrammatic order: *p* ⨾ *q* = *multiply*(*q*,*p*). */
    @targetName("sequenceExt")
    final def >>[C: Obj](q: P[B, C]): P[A, C] = {
      multiply(q, p)
    }

  /** Laws that any `Promonad` must satisfy beyond the [[Category.CategoryLaws]] of [[category]]. */
  object PromonadLaws {

    /** *unit*(*g* ∘ *f*) = *unit*(*g*) ∘ *unit*(*f*)
      */
    def unitComposition[A: Obj, B: Obj, C: Obj](f: A --> B, g: B --> C)(using P[A, C] is Observable): Boolean = {
      unit(K.compose(g, f)) =?= multiply(unit(g), unit(f))
    }

    /** If *f* = *f*′, then *unit*(*f*) = *unit*(*f*′).
      *
      * @note The premise is not checked: *f*′ must be equal to *f* by construction.
      */
    def unitCongruence[A: Obj, B: Obj](f: A --> B, f2: A --> B)(using P[A, B] is Observable): Boolean = {
      unit(f) =?= unit(f2)
    }
  }
}

object Promonad {

  /** The category of arrows of a promonad *P*. */
  final class Underlying(tracked val P: Promonad) extends Category {
    type Self = P.P
    type Obj  = P.K.Obj

    def identity[A: Obj]: A --> A = {
      P.identity[A]
    }

    def compose[A: Obj, B: Obj, C: Obj](g: B --> C, f: A --> B): A --> C = {
      P.multiply(g, f)
    }
  }

  /** The opposite *P*ᵒᵖ of a promonad *P* over **K**: a promonad over **K**ᵒᵖ, with every arrow reversed. */
  final class Op(tracked val Q: Promonad) extends Promonad(Q.K.op) {
    import Q.K.Obj

    type Self[A, B] = Q.P[B, A]

    def unit[A: Obj, B: Obj](f: Q.K.-->[B, A]): Q.P[B, A] = {
      Q.unit(f)
    }

    def multiply[A: Obj, B: Obj, C: Obj](g: Q.P[C, B], f: Q.P[B, A]): Q.P[C, A] = {
      Q.multiply(f, g)
    }
  }

  /** The hom promonad of a category **K**: its arrows are the morphisms of **K** itself. */
  open class Hom(tracked override val K: Category) extends Promonad(K) {
    import K.{Obj, -->}

    type Self = K.Hom

    def unit[A: Obj, B: Obj](f: A --> B): A --> B = {
      f
    }

    def multiply[A: Obj, B: Obj, C: Obj](g: B --> C, f: A --> B): A --> C = {
      K.compose(g, f)
    }
  }
}
