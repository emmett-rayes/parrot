package parrot
package category

import scala.annotation.targetName

/** A category whose objects are types and whose morphisms are values.
  *
  * Represents a category **C**, where
  *   - the objects are types *A* of kind * with evidence that they belong to a type class `Obj`
  *   - **C**(*A*,*B*) are the morphisms *f*: *A* → *B*
  *   - *id*: *A* → *A* is the identity
  *   - ∘ is the composition
  *
  * @note Identity and composition are single polymorphic programs, so the category is uniform. Equality of morphisms is
  *   observational equality, which the laws check through an [[Observable]] instance.
  */
abstract class Category extends caps.Pure {
  type Self[_, _]

  /** The type class selecting the objects: any refinement of [[Type]]. */
  type Obj <: Type

  /** The morphisms **C**(*A*,*B*). */
  final type Hom = Self

  /** Infix alias for [[Hom]]. */
  final type --> = Hom

  /** The identity morphism *id*: *A* → *A*. */
  def identity[A: Obj]: A --> A

  /** Composes *g*: *B* → *C* and *f*: *A* → *B* to *g* ∘ *f*: *A* → *C*. */
  def compose[A: Obj, B: Obj, C: Obj](g: B --> C, f: A --> B): A --> C

  /** Composes *g*: *B* → *C* and *f*: *A* → *B* in diagrammatic order to *f* ⨾ *g*: *A* → *C*. */
  final def andThen[A: Obj, B: Obj, C: Obj](f: A --> B, g: B --> C): A --> C = {
    compose(g, f)
  }

  /** An isomorphism *A* ≅ *B* between objects *A* and *B*.
    *
    * Consists of two morphisms, inverse to each other by [[IsoLaws.isomorphism]].
    */
  final case class Iso[A: Obj, B: Obj](to: A --> B, from: B --> A)

  /** Infix alias for [[Iso]]. */
  final type <-> = Iso

  /** The corresponding opposite category **C**ᵒᵖ. */
  final lazy val op: Category.Op { val K: Category.this.type } = Category.Op(this)

  extension [B: Obj, C: Obj](g: B --> C)
    /** Infix extension for [[compose]]. */
    @targetName("composeExt")
    final def <<<[A: Obj](f: A --> B): A --> C = {
      Category.this.compose(g, f)
    }

  extension [A: Obj, B: Obj](f: A --> B)
    /** Infix extension for [[andThen]]. */
    @targetName("andThenExt")
    final def >>>[C: Obj](g: B --> C): A --> C = {
      Category.this.andThen(f, g)
    }

  /** Laws that any `Category` must satisfy.
    *
    * Category composition is associative, and identities act as left and right units. Composition is also congruent
    * with respect to observational equality of morphisms.
    */
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
      * @note The premise is not checked: *f*′ and *g*′ must be equal to *f* and *g* by construction.
      */
    def congruence[A: Obj, B: Obj, C: Obj](f: A --> B, f2: A --> B, g: B --> C, g2: B --> C)(
      using (A --> C) is Observable
    ): Boolean = {
      (f >>> g) =?= (f2 >>> g2)
    }
  }

  /** Laws that any `Iso` must satisfy. */
  object IsoLaws {

    /** *i*⁻¹ ∘ *i* = *id* and *i* ∘ *i*⁻¹ = *id*
      */
    def isomorphism[A: Obj, B: Obj](i: A <-> B)(using (A --> A) is Observable, (B --> B) is Observable): Boolean = {
      ((i.to >>> i.from) =?= identity[A]) && ((i.from >>> i.to) =?= identity[B])
    }
  }
}

object Category {

  /** The opposite **K**ᵒᵖ of a category **K**.
    *
    * The opposite category has the same objects and identities, with every morphism reversed.
    */
  final class Op(tracked val K: Category) extends Category {
    type Self[A, B] = K.Hom[B, A]
    type Obj        = K.Obj

    def identity[A: Obj]: A --> A = {
      K.identity[A]
    }

    def compose[A: Obj, B: Obj, C: Obj](g: B --> C, f: A --> B): A --> C = {
      K.compose(f, g)
    }
  }

  /** The product category **C₁** × **C₂** of two categories.
    *
    * Represents a category, where
    *   - the objects are the pair types *X* = (*X*₁,*X*₂) whose components are objects of **C₁** and **C₂**
    *   - the morphisms are pairs of morphisms in (**C₁** × **C₂**)(*X*,*Y*) = **C₁**(*X*₁,*Y*₁) × **C₂**(*X*₂,*Y*₂)
    *     whose components are morphisms of **C₁** and **C₂**
    *   - the identity is componentwise: *id* = (*id*,*id*)
    *   - the composition is componentwise: (*g*₁,*g*₂) ∘ (*f*₁,*f*₂) = (*g*₁ ∘ *f*₁,*g*₂ ∘ *f*₂)
    *
    * @note A morphism type is computed from two object types, so the components of a pair type *X* are taken apart by
    *   the match types [[Product.Fst]] and [[Product.Snd]]. The object evidence ([[ProductObj]]) is stated about the
    *   components themselves, so generic code never needs a match type to reduce; on a pair type (*A*₁,*A*₂) they
    *   reduce to *A*₁ and *A*₂.
    */
  final class Product(tracked val C1: Category, tracked val C2: Category) extends Category {
    import Product.{Fst, Snd}

    type Self[X, Y] = (C1.Hom[Fst[X], Fst[Y]], C2.Hom[Snd[X], Snd[Y]])

    /** Evidence that a pair type is an object: its components are objects of **C₁** and **C₂**. */
    trait ProductObj extends Type {

      /** The first component is an object of **C₁**. */
      def fst: Fst[ProductObj.this.Self] is C1.Obj

      /** The second component is an object of **C₂**. */
      def snd: Snd[ProductObj.this.Self] is C2.Obj
    }

    type Obj = ProductObj

    /** Pairs of objects are objects. */
    given PairIsObj: [A1: C1.Obj as first, A2: C2.Obj as second] => ((A1, A2) is ProductObj) {
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
