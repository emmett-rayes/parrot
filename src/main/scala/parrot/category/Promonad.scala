package parrot
package category

import scala.annotation.targetName

/** A promonad on **K** valued in 𝒮.
  *
  * Represents a promonad (*P*, *η*, *μ*), where
  *   - *η*: **K**(*A*,*B*) → *P*(*A*,*B*), the unit
  *   - *μ*: *P*(*B*,*C*) × *P*(*A*,*B*) → *P*(*A*,*C*), the multiplication
  */
abstract class Promonad(tracked override val K: Category) extends Endoprofunctor(K, Total) {
  import K.{Obj, -->}
  import K.op.--> as ~~>

  /** The unit *η*: **K**(*A*,*B*) → *P*(*A*,*B*).
    *
    * This is the identity-on-objects functor from **K** to the category induced by *P*. See [[category]].
    */
  def unit[A: Obj, B: Obj](f: A --> B): P[A, B]

  /** The multiplication *μ*: *P*(*B*,*C*) × *P*(*A*,*B*) → *P*(*A*,*C*). */
  def multiply[A: Obj, B: Obj, C: Obj](g: P[B, C], f: P[A, B]): P[A, C]

  /** Arrows are values of 𝒮, so every arrow type is an object of 𝒮. */
  final def objects[A: Obj, B: Obj]: P[A, B] is Type = {
    Type.TIsType
  }

  /** *P*(*f*,*g*)(*p*) = *η*(*g*) ∘ *p* ∘ *η*(*f*)
    */
  override def bimap[A1: Obj, B1: Obj, A2: Obj, B2: Obj](f: A1 ~~> A2, g: B1 --> B2): P[A1, B1] -> P[A2, B2] = {
    p => multiply(unit(g), multiply(p, unit[A2, A1](f)))
  }

  /** The identity arrow *η*(*id*). */
  final def identity[A: Obj]: P[A, A] = {
    unit(K.identity[A])
  }

  /** Composes *P*(*B*,*C*) and *P*(*A*,*B*) to *P*(*A*,*C*). */
  final def compose[A: Obj, B: Obj, C: Obj](q: P[B, C], p: P[A, B]): P[A, C] = {
    multiply(q, p)
  }

  /** Composes *P*(*A*,*B*) and *P*(*B*,*C*) to *P*(*A*,*C*) in the diagrammatic order. */
  final def andThen[A: Obj, B: Obj, C: Obj](p: P[A, B], q: P[B, C]): P[A, C] = {
    compose(q, p)
  }

  /** Every profunctor induces a category of arrows, where the objects are the objects of **K**, the morphisms are
    * *P*(*A*,*B*), the identity is given by *η*, and composition is given by *μ*.
    */
  final lazy val category: Promonad.Arrows { val P: Promonad.this.type } = Promonad.Arrows(this)

  extension [B: Obj, C: Obj](q: P[B, C])
    /** Infix extension for [[compose]]. */
    @targetName("composeExt")
    final def <<<[A: Obj](p: P[A, B]): P[A, C] = {
      compose(q, p)
    }

  extension [A: Obj, B: Obj](p: P[A, B])
    /** Infix extension for [[andThen]]. */
    @targetName("andThenExt")
    final def >>>[C: Obj](q: P[B, C]): P[A, C] = {
      andThen(p, q)
    }

  /** Laws that any `Promonad` must satisfy. */
  object PromonadLaws {

    /** *η*(*g* ∘ *f*) = *η*(*g*) ∘ *η*(*f*)
      */
    def unitComposition[A: Obj, B: Obj, C: Obj](f: A --> B, g: B --> C)(using P[A, C] is Observable): Boolean = {
      unit(f >>> g) =?= (unit(f) >>> unit(g))
    }

    /** If *f* = *f*′, then *η*(*f*) = *η*(*f*′).
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
  open class Arrows(tracked val P: Promonad) extends Category {
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

  /** The hom promonad of a category **K**.
    *
    * The hom promonad's arrows are the morphisms of **K** itself.
    */
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
