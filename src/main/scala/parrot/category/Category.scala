package parrot
package category

import scala.annotation.targetName

/** A category whose objects are types and whose morphisms are values.
  *
  * Represents a category **C**, where
  *   - the objects are the types *A* with evidence that *A* is an object
  *   - **C**(*A*,*B*) are the morphisms *f*: *A* → *B*
  *   - *id*: *A* → *A* is the identity
  *   - ∘ is the composition
  *
  * Identity and composition are single polymorphic programs, so the category is uniform: they may use the evidence of
  * their objects, but they cannot inspect the objects themselves. Equality of morphisms is semantic equality, which the
  * laws check through an [[Observable]].
  */
abstract class Category extends caps.Pure {
  type Self[_, _]

  /** The morphisms **C**(*A*,*B*). */
  final type Hom = Self

  /** Infix alias for [[Hom]]. */
  final type --> = Hom

  /** The type class selecting the objects: any refinement of [[Type]]. */
  type Obj <: Type

  /** The identity morphism *id*: *A* → *A*. */
  def identity[A: Obj]: A --> A

  /** Composes *g*: *B* → *C* and *f*: *A* → *B* to *g* ∘ *f*: *A* → *C*. */
  def compose[A: Obj, B: Obj, C: Obj](g: B --> C, f: A --> B): A --> C

  /** An isomorphism between *A* and *B*: two morphisms, inverse to each other by [[CategoryLaws.isomorphism]]. */
  final case class Iso[A, B](to: A --> B, from: B --> A)

  /** Infix alias for [[Iso]]: *A* ≅ *B*. */
  final type <-> = Iso

  /** The opposite category **C**ᵒᵖ: the same objects, with every morphism reversed. */
  final lazy val op: Category.Op { val K: Category.this.type } = Category.Op(this)

  extension [A: Obj, B: Obj](f: A --> B)
    /** Composes in diagrammatic order: *f* ⨾ *g* = *g* ∘ *f*. */
    @targetName("andThenExt")
    final def >>>[C: Obj](g: B --> C): A --> C = {
      Category.this.compose(g, f)
    }

  /** Laws that any `Category` must satisfy. */
  object CategoryLaws {

    /** *id* ∘ *f* = *f*
      */
    def leftIdentity[A: Obj, B: Obj](f: A --> B)(using (A --> B) is Observable): Boolean = {
      (f >>> identity[B]) =?= f
    }

    /** *f* ∘ *id* = *f*
      */
    def rightIdentity[A: Obj, B: Obj](f: A --> B)(using (A --> B) is Observable): Boolean = {
      (identity[A] >>> f) =?= f
    }

    /** *h* ∘ (*g* ∘ *f*) = (*h* ∘ *g*) ∘ *f*
      */
    def associativity[A: Obj, B: Obj, C: Obj, D: Obj](f: A --> B, g: B --> C, h: C --> D)(
      using (A --> D) is Observable
    ): Boolean = {
      ((f >>> g) >>> h) =?= (f >>> (g >>> h))
    }

    /** If *f* = *f*′ and *g* = *g*′, then *g* ∘ *f* = *g*′ ∘ *f*′.
      *
      * @note The premise is not checked: *f*′ and *g*′ must be equal to *f* and *g* by construction (variants).
      */
    def congruence[A: Obj, B: Obj, C: Obj](f: A --> B, f2: A --> B, g: B --> C, g2: B --> C)(
      using (A --> C) is Observable
    ): Boolean = {
      (f >>> g) =?= (f2 >>> g2)
    }

    /** *i*⁻¹ ∘ *i* = *id* and *i* ∘ *i*⁻¹ = *id*
      */
    def isomorphism[A: Obj, B: Obj](i: A <-> B)(using (A --> A) is Observable, (B --> B) is Observable): Boolean = {
      ((i.to >>> i.from) =?= identity[A]) && ((i.from >>> i.to) =?= identity[B])
    }
  }
}

object Category {

  /** The opposite **K**ᵒᵖ of a category **K**: the same objects and identities, with every morphism reversed. */
  final class Op(tracked val K: Category) extends Category {
    type Self[A, B] = K.-->[B, A]
    type Obj        = K.Obj

    def identity[A: Obj]: A --> A = {
      K.identity[A]
    }

    def compose[A: Obj, B: Obj, C: Obj](g: B --> C, f: A --> B): A --> C = {
      K.compose(f, g)
    }
  }

  /** The product **C₁** × **C₂** of two categories: pairs of objects, and pairs of morphisms composed componentwise.
    *
    * Represents a category, where
    *   - the objects are the pair types *X* = (*X*₁,*X*₂) whose components are objects of **C₁** and **C₂**
    *   - (**C₁** × **C₂**)(*X*,*Y*) = **C₁**(*X*₁,*Y*₁) × **C₂**(*X*₂,*Y*₂)
    *   - *id* = (*id*,*id*) and (*g*₁,*g*₂) ∘ (*f*₁,*f*₂) = (*g*₁ ∘ *f*₁,*g*₂ ∘ *f*₂)
    *
    * A morphism type is computed from two object types, so the components of a pair type *X* are taken apart by the
    * match types [[Product.Fst]] and [[Product.Snd]]. The object evidence ([[Components]])
    * is stated about the components themselves, so generic code never needs a match type to reduce; on a pair type
    * (*A*₁,*A*₂) they reduce to *A*₁ and *A*₂. A [[Bifunctor]] is a functor out of a product category,
    * [[Bifunctor.functor]].
    */
  final class Product(tracked val C1: Category, tracked val C2: Category) extends Category {
    import Product.{Fst, Snd}

    type Self[X, Y] = (C1.-->[Fst[X], Fst[Y]], C2.-->[Snd[X], Snd[Y]])

    /** Evidence that a pair type is an object: its components are objects of **C₁** and **C₂**. */
    trait Components extends Type {

      /** The first component is an object of **C₁**. */
      def fst: Fst[Components.this.Self] is C1.Obj

      /** The second component is an object of **C₂**. */
      def snd: Snd[Components.this.Self] is C2.Obj
    }

    type Obj = Components

    /** Pairs of objects are objects. */
    given PairIsObj: [A1, A2] => (first: A1 is C1.Obj, second: A2 is C2.Obj) => ((A1, A2) is Components) {
      def fst: A1 is C1.Obj = first
      def snd: A2 is C2.Obj = second
    }

    def identity[X: Obj]: X --> X = {
      (C1.identity[Fst[X]](using X.fst), C2.identity[Snd[X]](using X.snd))
    }

    def compose[X: Obj, Y: Obj, Z: Obj](g: Y --> Z, f: X --> Y): X --> Z = {
      (C1.compose(g._1, f._1)(using X.fst, Y.fst, Z.fst), C2.compose(g._2, f._2)(using X.snd, Y.snd, Z.snd))
    }
  }

  object Product {

    /** The first component of a pair type. */
    type Fst[X] = X match {
      case (a, b) => a
    }

    /** The second component of a pair type. */
    type Snd[X] = X match {
      case (a, b) => b
    }
  }
}
