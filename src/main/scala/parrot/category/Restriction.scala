package parrot
package category

import scala.annotation.targetName

/** A restriction structure on a category **C**.
  *
  * Represents a restriction category (Cockett–Lack), where
  *   - *f̄*: *A* → *A* is the restriction of *f*: *A* → *B*
  *   - *f* is total when *f̄* = *id*
  */
abstract class Restriction(tracked val category: Category) extends caps.Pure {
  import category.{Obj, identity, -->, >>>}

  /** The restriction *f̄*: *A* → *A* of *f*: *A* → *B*.
    *
    * This is the partial identity on the inputs where *f* is defined.
    */
  def restrict[A: Obj, B: Obj](f: A --> B): A --> A

  extension [A: Obj, B: Obj](f: A --> B)
    /** Postfix form of [[restrict]]. */
    @targetName("restrictExt")
    final def restricted: A --> A = {
      restrict(f)
    }

  /** Laws that any `Restriction` must satisfy. */
  object RestrictionLaws {

    /** *f* ∘ *f̄* = *f*
      */
    def r1[A: Obj, B: Obj](f: A --> B)(using (A --> B) is Observable): Boolean = {
      (restrict(f) >>> f) =?= f
    }

    /** *ḡ* ∘ *f̄* = *f̄* ∘ *ḡ*
      */
    def r2[A: Obj, B: Obj, C: Obj](f: A --> B, g: A --> C)(
      using (A --> A) is Observable
    ): Boolean = {
      (restrict(f) >>> restrict(g)) =?= (restrict(g) >>> restrict(f))
    }

    /** (*g* ∘ *f̄*)‾ = *ḡ* ∘ *f̄*
      */
    def r3[A: Obj, B: Obj, C: Obj](f: A --> B, g: A --> C)(
      using (A --> A) is Observable
    ): Boolean = {
      restrict(restrict(f) >>> g) =?= (restrict(f) >>> restrict(g))
    }

    /** *ḡ* ∘ *f* = *f* ∘ (*g* ∘ *f*)‾
      */
    def r4[A: Obj, B: Obj, C: Obj](f: A --> B, g: B --> C)(
      using (A --> B) is Observable
    ): Boolean = {
      (f >>> restrict(g)) =?= (restrict(f >>> g) >>> f)
    }

    /** *J*(*f*)‾ = *id*
      *
      * The functor *J*: **D** → **C** lands in the total morphisms.
      *
      * @note Not every functor into **C** does: the law is for the functors that pick out pure morphisms, such as
      *   [[Promonad.pure]] and the inclusion of 𝒮 in 𝒫.
      */
    def pureTotal(functor: Functor.Into[category.type])[A: functor.source.Obj, B: functor.source.Obj](
      f: functor.source.Hom[A, B]
    )(using (functor.F[A] --> functor.F[A]) is Observable): Boolean = {
      given FAIsObj: (functor.F[A] is Obj) = functor.objects[A]
      given FBIsObj: (functor.F[B] is Obj) = functor.objects[B]
      restrict(functor.map(f)) =?= identity[functor.F[A]]
    }

    /** If *f* = *f*′, then *f̄* = *f*′‾.
      *
      * @note The premise is not checked: *f*′ must be equal to *f* by construction.
      */
    def congruence[A: Obj, B: Obj](f: A --> B, f2: A --> B)(
      using (A --> A) is Observable
    ): Boolean = {
      restrict(f) =?= restrict(f2)
    }
  }
}

object Restriction {

  /** The restriction structures on a category **C**. */
  type On[C <: Category] = Restriction { val category: C }
}
