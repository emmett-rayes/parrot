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

  /** The type class selecting the objects. */
  type Obj <: Category.Type

  /** The hom-object of **C**. */
  final type Hom = Self

  /** Infix alias for [[Hom]]. */
  final type --> = Hom

  /** An object of the category. */
  final type Object = Category.Object { val category: Category.this.type }

  /** The object *X* of the category, specified by its evidence. */
  final def Object[X: Obj]: X is Object = {
    new Category.Object(this) {
      type Self = X

      def evidence: X is Obj = summon
    }
  }

  /** The identity morphism *id*: *A* → *A*. */
  def identity[A: Obj]: A --> A

  /** Composes *g*: *B* → *C* and *f*: *A* → *B* to *g* ∘ *f*: *A* → *C*. */
  def compose[A: Obj, B: Obj, C: Obj](g: B --> C, f: A --> B): A --> C

  /** Composes *f*: *A* → *B* and *g*: *B* → *C* in diagrammatic order to *f* ⨾ *g*: *A* → *C*. */
  final def andThen[A: Obj, B: Obj, C: Obj](f: A --> B, g: B --> C): A --> C = {
    compose(g, f)
  }

  /** An isomorphism *A* ≅ *B* between objects *A* and *B*.
    *
    * An isomorphism consists of two morphisms, inverse to each other. See [[IsoLaws]].
    */
  final case class Iso[A: Obj, B: Obj](to: A --> B, from: B --> A)

  /** Infix alias for [[Iso]]. */
  final type <-> = Iso

  /** The corresponding opposite category **C**ᵒᵖ. */
  final lazy val op: Category.Op.Of[this.type] = Category.Op(this)

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

    /** *i*⁻¹ ∘ *i* = *id*
      */
    def leftInverse[A: Obj, B: Obj](i: A <-> B)(using (A --> A) is Observable): Boolean = {
      ((i.to >>> i.from) =?= identity[A])
    }

    /** *i* ∘ *i*⁻¹ = *id*
      */
    def rightInverse[A: Obj, B: Obj](i: A <-> B)(using (B --> B) is Observable): Boolean = {
      ((i.from >>> i.to) =?= identity[B])
    }
  }
}

object Category {

  /** A base trait for type classes.
    *
    * Used to represent evidence that a type belongs to a certain type class.
    */
  trait Type extends caps.Pure {
    type Self
  }

  object Type {

    /** Summons the `Type` instance of `T`. */
    def apply[T: Type]: T is Type = summon

    /** Every type of kind `*` is trivially a `Type`. */
    given TIsType: [T] => T is Type {}
  }

  /** An object of a category **C**.
    *
    * Represents an object *A* of **C**, where
    *   - *A* is a type, the carrier
    *   - the evidence shows that *A* is an object of **C**
    *
    * A structure on an object takes it as a parameter, which a refinement can ask more of: [[Monoidal]] is on an
    * object, and [[Cartesian]] refines it to a [[Terminal]] object, an object with `discard`.
    */
  abstract class Object(tracked val category: Category) extends caps.Pure {
    type Self

    /** The object *A*. */
    final type A = Self

    /** *A* is an object of **C**. */
    def evidence: A is category.Obj
  }

  /** The opposite **K**ᵒᵖ of a category **K**.
    *
    * The opposite category has the same objects and identities, with every morphism reversed.
    */
  final class Op(tracked val category: Category) extends Category {
    type Self[A, B] = category.Hom[B, A]
    type Obj        = category.Obj

    def identity[A: Obj]: A --> A = {
      category.identity[A]
    }

    def compose[A: Obj, B: Obj, C: Obj](g: B --> C, f: A --> B): A --> C = {
      category.compose(f, g)
    }
  }

  object Op {

    /** The opposite of a category **K**. */
    type Of[K <: Category] = Op { val category: K }
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
    *   the match types [[Product.Fst]] and [[Product.Snd]]. The object evidence ([[Pair]]) is stated about the
    *   components themselves, so generic code never needs a match type to reduce; on a pair type (*A*₁,*A*₂) they
    *   reduce to *A*₁ and *A*₂.
    */
  final class Product(tracked val factor1: Category, tracked val factor2: Category) extends Category {
    import Product.{Fst, Snd}

    type Self[X, Y] = (factor1.Hom[Fst[X], Fst[Y]], factor2.Hom[Snd[X], Snd[Y]])
    type Obj        = Pair

    /** Evidence that a pair type is an object: its components are objects of **C₁** and **C₂**. */
    trait Pair extends Type {

      /** The first component is an object of **C₁**. */
      def fst: Fst[Pair.this.Self] is factor1.Obj

      /** The second component is an object of **C₂**. */
      def snd: Snd[Pair.this.Self] is factor2.Obj
    }

    /** Pairs of objects are objects. */
    given PairIsObj: [A1: factor1.Obj as first, A2: factor2.Obj as second] => ((A1, A2) is Pair) {
      def fst: A1 is factor1.Obj = first
      def snd: A2 is factor2.Obj = second
    }

    def identity[X: Pair]: X --> X = {
      (factor1.identity[Fst[X]](using X.fst), factor2.identity[Snd[X]](using X.snd))
    }

    def compose[X: Pair, Y: Pair, Z: Pair](g: Y --> Z, f: X --> Y): X --> Z = {
      (factor1.compose(g._1, f._1)(using X.fst, Y.fst, Z.fst), factor2.compose(g._2, f._2)(using X.snd, Y.snd, Z.snd))
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

  /** The empty category **0**.
    *
    * Represents **0**, where
    *   - there are no objects
    *   - there are no morphisms
    *
    * Identity and composition take evidence of an object, so they can never be called.
    */
  object Empty extends Category {
    type Self[A, B] = Nothing
    type Obj        = Absurd

    /** Evidence that a type is an object of **0**. */
    trait Absurd extends Type {

      /** A value of `Nothing`, from which anything follows. */
      def absurd: Nothing
    }

    def identity[A: Absurd]: A --> A = {
      A.absurd
    }

    def compose[A: Absurd, B: Absurd, C: Absurd](g: B --> C, f: A --> B): A --> C = {
      A.absurd
    }
  }

  /** The discrete category **2**, with two objects and only their identities.
    *
    * Represents **2**, where
    *   - the objects are the literal types `0` and `1`
    *   - **2**(*A*,*B*) contains the identity morphism if *A* = *B*, and no morphisms otherwise
    *   - *id* is the identity morphism for each object
    */
  object Discrete2 extends Category {
    type Self = =:=
    type Obj  = Disc2

    /** Evidence that a type is an object of **2**. */
    trait Disc2 extends Type {

      /** The object, as an index: `Index.Zero` if it is `0`, `Index.One` if it is `1`. */
      def index: Disc2.Index[Disc2.this.Self]
    }

    object Disc2 {

      /** The indices of the objects of **2**.
        *
        * Matching on an `Index[A]` tells which object *A* is.
        */
      enum Index[A] extends caps.Pure {
        case Zero extends Index[0]
        case One  extends Index[1]
      }

      /** `0` is an object of **2**. */
      given Zero: (0 is Disc2) {
        def index: Index[0] = Index.Zero
      }

      /** `1` is an object of **2**. */
      given One: (1 is Disc2) {
        def index: Index[1] = Index.One
      }
    }

    def identity[A: Disc2]: A =:= A = {
      summon
    }

    def compose[A: Disc2, B: Disc2, C: Disc2](g: B =:= C, f: A =:= B): A =:= C = {
      g.compose(f)
    }
  }
}
