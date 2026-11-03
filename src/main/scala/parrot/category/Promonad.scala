package parrot
package category

import scala.annotation.targetName

import Category.Type

/** A promonad on **C** valued in 𝒮.
  *
  * Represents a promonad (*P*, *η*, *μ*), where
  *   - *η*: **C**(*A*,*B*) → *P*(*A*,*B*), the unit
  *   - *μ*: *P*(*B*,*C*) × *P*(*A*,*B*) → *P*(*A*,*C*), the multiplication
  */
abstract class Promonad(tracked override val category: Category) extends Endoprofunctor(category, Total) {
  import category.{Obj, -->}
  import category.op.--> as ~~>

  /** The unit *η*: **C**(*A*,*B*) → *P*(*A*,*B*).
    *
    * This is the identity-on-objects functor from **C** to the category induced by *P*. See [[arrows]].
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
  override def bimap[A1: Obj, A2: Obj, B1: Obj, B2: Obj](f: A1 ~~> B1, g: A2 --> B2): P[A1, A2] -> P[B1, B2] = {
    p => multiply(unit(g), multiply(p, unit[B1, A1](f)))
  }

  /** The identity arrow *η*(*id*). */
  final def identity[A: Obj]: P[A, A] = {
    unit(category.identity[A])
  }

  /** Composes *P*(*B*,*C*) and *P*(*A*,*B*) to *P*(*A*,*C*). */
  final def compose[A: Obj, B: Obj, C: Obj](q: P[B, C], p: P[A, B]): P[A, C] = {
    multiply(q, p)
  }

  /** Composes *P*(*A*,*B*) and *P*(*B*,*C*) to *P*(*A*,*C*) in the diagrammatic order. */
  final def andThen[A: Obj, B: Obj, C: Obj](p: P[A, B], q: P[B, C]): P[A, C] = {
    compose(q, p)
  }

  /** Every profunctor induces a category of arrows, where the objects are the objects of **C**, the morphisms are
    * *P*(*A*,*B*), the identity is given by *η*, and composition is given by *μ*.
    */
  final lazy val arrows: Promonad.Arrows.Of[this.type] = Promonad.Arrows(this)

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

  /** The promonads on a category **C**. */
  type On[C <: Category] = Promonad { val category: C }

  /** The category of arrows of a promonad *P*. */
  open class Arrows(tracked val promonad: Promonad) extends Category {
    type Self = promonad.P
    type Obj  = promonad.category.Obj

    def identity[A: Obj]: A --> A = {
      promonad.identity[A]
    }

    def compose[A: Obj, B: Obj, C: Obj](g: B --> C, f: A --> B): A --> C = {
      promonad.multiply(g, f)
    }
  }

  object Arrows {

    /** The category of arrows of a promonad *P*. */
    type Of[P <: Promonad] = Arrows { val promonad: P }
  }

  /** The opposite *P*ᵒᵖ of a promonad *P* over **C**: a promonad over **C**ᵒᵖ, with every arrow reversed. */
  final class Op(tracked val promonad: Promonad) extends Promonad(promonad.category.op) {
    import promonad.category.Obj

    type Self[A, B] = promonad.P[B, A]

    def unit[A: Obj, B: Obj](f: promonad.category.-->[B, A]): promonad.P[B, A] = {
      promonad.unit(f)
    }

    def multiply[A: Obj, B: Obj, C: Obj](g: promonad.P[C, B], f: promonad.P[B, A]): promonad.P[C, A] = {
      promonad.multiply(f, g)
    }
  }

  /** The hom promonad of a category **C**.
    *
    * The hom promonad's arrows are the morphisms of **C** itself.
    */
  open class Hom(tracked override val category: Category) extends Promonad(category) {
    import category.{Obj, -->}

    type Self = category.Hom

    def unit[A: Obj, B: Obj](f: A --> B): A --> B = {
      f
    }

    def multiply[A: Obj, B: Obj, C: Obj](g: B --> C, f: A --> B): A --> C = {
      category.compose(g, f)
    }
  }
}
