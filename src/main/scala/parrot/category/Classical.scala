package parrot
package category

import scala.annotation.targetName

/** A classical restriction structure on a category **C**.
  *
  * Represents a classical restriction category (Cockett–Manes) with its override operator (Lemay–Nester), where
  *   - 0: *A* → *B* is the restriction zero, the nowhere-defined morphism
  *   - *f̄*ᶜ: *A* → *A* is the complement of *f̄*
  *   - *f* ⊳ *g*: *A* → *B* is the override operator
  *
  * In a classical restriction category, definedness is decidable. The override operator is unique, and on compatible
  * morphisms *f* and *g* it is their join *f* ∨ *g*.
  *
  * @see docs/TUTORIAL.md §18.4
  */
abstract class Classical(tracked override val category: Category) extends Restriction(category) {
  import category.{Obj, -->, >>>}

  /** The restriction zero 0: *A* → *B*. */
  def zero[A: Obj, B: Obj]: A --> B

  /** The complement *f̄*ᶜ: *A* → *A* of *f*: *A* → *B*.
    *
    * *f̄*ᶜ is defined exactly where *f* is not.
    */
  def complement[A: Obj, B: Obj](f: A --> B): A --> A

  /** The override *f* ⊳ *g*: *A* → *B* of *f*: *A* → *B* and *g*: *A* → *B*.
    *
    * Runs *f* where it is defined and *g* elsewhere.
    */
  def orElse[A: Obj, B: Obj](f: A --> B, g: A --> B): A --> B

  extension [A: Obj, B: Obj](f: A --> B)
    /** Infix extension for [[orElse]]. */
    @targetName("orElseExt")
    final def |>(g: A --> B): A --> B = {
      orElse(f, g)
    }

  /** Laws that any `Classical` restriction structure must satisfy. */
  object ClassicalLaws {

    /** 0‾ = 0 */
    def zeroRestriction[A: Obj, B: Obj](using (A --> A) is Observable): Boolean = {
      restrict(zero[A, B]) =?= zero[A, A]
    }

    /** 0 ∘ *f* = 0 */
    def zeroLeft[A: Obj, B: Obj, C: Obj](f: A --> B)(using (A --> C) is Observable): Boolean = {
      (f >>> zero[B, C]) =?= zero[A, C]
    }

    /** *f* ∘ 0 = 0
      */
    def zeroRight[A: Obj, B: Obj, C: Obj](f: B --> C)(using (A --> C) is Observable): Boolean = {
      (zero[A, B] >>> f) =?= zero[A, C]
    }

    /** 0 ⊳ *f* = *f* = *f* ⊳ 0 */
    def overrideZero[A: Obj, B: Obj](f: A --> B)(using (A --> B) is Observable): Boolean = {
      (orElse(zero[A, B], f) =?= f) && (orElse(f, zero[A, B]) =?= f)
    }

    /** (*f* ⊳ *g*) ⊳ *h* = *f* ⊳ (*g* ⊳ *h*) (**⊳.1**)
      */
    def overrideAssociativity[A: Obj, B: Obj](f: A --> B, g: A --> B, h: A --> B)(
      using (A --> B) is Observable
    ): Boolean = {
      orElse(orElse(f, g), h) =?= orElse(f, orElse(g, h))
    }

    /** *f* ⊳ (*g* ∘ *f̄*) = *f* (**⊳.2**)
      */
    def overrideRestricted[A: Obj, B: Obj](f: A --> B, g: A --> B)(
      using (A --> B) is Observable
    ): Boolean = {
      orElse(f, restrict(f) >>> g) =?= f
    }

    /** (*f* ∘ *ḡ*) ⊳ *f* = *f* (**⊳.3**)
      */
    def overrideRestricting[A: Obj, B: Obj, C: Obj](f: A --> B, g: A --> C)(
      using (A --> B) is Observable
    ): Boolean = {
      orElse(restrict(g) >>> f, f) =?= f
    }

    /** (*f* ⊳ *g*) ∘ *h* = (*f* ∘ *h*) ⊳ (*g* ∘ *h*) (**⊳.4**)
      *
      * Precomposition distributes over ⊳.
      */
    def overridePrecomposition[A: Obj, B: Obj, C: Obj](
      h: A --> B,
      f: B --> C,
      g: B --> C,
    )(using (A --> C) is Observable): Boolean = {
      (h >>> orElse(f, g)) =?= orElse(h >>> f, h >>> g)
    }

    /** *h* ∘ (*f* ⊳ *g*)‾ = (*h* ∘ *f̄*) ⊳ (*h* ∘ *ḡ*) (**⊳.5**)
      */
    def overrideRestriction[A: Obj, B: Obj, C: Obj](
      f: A --> B,
      g: A --> B,
      h: A --> C,
    )(using (A --> C) is Observable): Boolean = {
      (restrict(orElse(f, g)) >>> h) =?= orElse(restrict(f) >>> h, restrict(g) >>> h)
    }

    /** *f̄*ᶜ ∘ *f̄* = 0
      *
      * A morphism cannot be both defined and undefined.
      */
    def complementExclusion[A: Obj, B: Obj](f: A --> B)(using (A --> A) is Observable): Boolean = {
      (restrict(f) >>> complement(f)) =?= zero[A, A]
    }

    /** *f̄* ⊳ *f̄*ᶜ = *id*
      *
      * Every input either is or is not in the domain of *f*.
      */
    def complementCover[A: Obj, B: Obj](f: A --> B)(using (A --> A) is Observable): Boolean = {
      orElse(restrict(f), complement(f)) =?= category.identity[A]
    }

    /** (*f̄*ᶜ)‾ = *f̄*ᶜ
      *
      * A complement is a restriction idempotent.
      */
    def complementRestriction[A: Obj, B: Obj](f: A --> B)(using (A --> A) is Observable): Boolean = {
      restrict(complement(f)) =?= complement(f)
    }

    /** (*f̄*ᶜ)ᶜ = *f̄* */
    def doubleComplement[A: Obj, B: Obj](f: A --> B)(using (A --> A) is Observable): Boolean = {
      complement(complement(f)) =?= restrict(f)
    }

    /** If *f* = *f*′ and *g* = *g*′, then *f* ⊳ *g* = *f*′ ⊳ *g*′ and *f̄*ᶜ = *f*′‾ᶜ.
      *
      * @note The premise is not checked: *f*′ and *g*′ must be equal to *f* and *g* by construction.
      */
    def congruence[A: Obj, B: Obj](f: A --> B, f2: A --> B, g: A --> B, g2: A --> B)(
      using
      (A --> B) is Observable,
      (A --> A) is Observable,
    ): Boolean = {
      (orElse(f, g) =?= orElse(f2, g2)) && (complement(f) =?= complement(f2))
    }

    /** Laws that follow from the others: theorems, checked as tests. */
    object Consequences {

      /** *f* ⊳ *g* = *g* ⊳ *f*
        *
        * Override is commutative on compatible morphisms, where it is their join (Lemay–Nester).
        *
        * @note Holds for compatible *f* and *g*, which agree where both are defined: *g* ∘ *f̄* = *f* ∘ *ḡ*. The premise
        *   is not checked: *f* and *g* must be built to be compatible.
        */
      def overrideCommutes[A: Obj, B: Obj](f: A --> B, g: A --> B)(using (A --> B) is Observable): Boolean = {
        orElse(f, g) =?= orElse(g, f)
      }
    }
  }
}

object Classical {

  /** The classical restriction structures on a category **C**. */
  type On[C <: Category] = Classical { val category: C }
}
