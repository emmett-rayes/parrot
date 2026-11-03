package parrot
package category

/** A coproduct of two objects of a category **C**.
  *
  * Represents a coproduct *S* = *A*₁ + *A*₂, where
  *   - *ι*₁: *A*₁ → *S* and *ι*₂: *A*₂ → *S* are the injections
  *   - [*f*,*g*]: *S* → *X* is the copairing of *f*: *A*₁ → *X* and *g*: *A*₂ → *X*, the unique morphism with [*f*,*g*]
  *     ∘ *ι*₁ = *f* and [*f*,*g*] ∘ *ι*₂ = *g*
  */
abstract class Coproduct(
  tracked val category: Category,
  tracked val summand1: category.Object,
  tracked val summand2: category.Object,
  tracked val apex: category.Object,
) extends caps.Pure {
  import category.{Obj, -->, >>>}

  /** The first summand *A*₁. */
  final type A1 = summand1.A

  /** The second summand *A*₂. */
  final type A2 = summand2.A

  /** The coproduct *S*. */
  final type S = apex.A

  private given A1IsObj: (A1 is Obj) = summand1.evidence

  private given A2IsObj: (A2 is Obj) = summand2.evidence

  private given SIsObj: (S is Obj) = apex.evidence

  /** The first injection *ι*₁: *A*₁ → *S*. */
  def inl: A1 --> S

  /** The second injection *ι*₂: *A*₂ → *S*. */
  def inr: A2 --> S

  /** The copairing [*f*,*g*]: *S* → *X* of *f*: *A*₁ → *X* and *g*: *A*₂ → *X*. */
  def copair[X: Obj](f: A1 --> X, g: A2 --> X): S --> X

  /** The coproduct as a colimit of the diagram (*A*₁,*A*₂) of shape **2**: its legs are the injections, and the
    * factorization of a cocone is the copairing of its legs.
    */
  final lazy val colimit: Coproduct.AsColimit.Of[this.type] = Coproduct.AsColimit(this)

  /** Laws that any `Coproduct` must satisfy. */
  object CoproductLaws {

    /** [*f*,*g*] ∘ *ι*₁ = *f*
      */
    def copairInl[X: Obj](f: A1 --> X, g: A2 --> X)(using (A1 --> X) is Observable): Boolean = {
      (inl >>> copair(f, g)) =?= f
    }

    /** [*f*,*g*] ∘ *ι*₂ = *g*
      */
    def copairInr[X: Obj](f: A1 --> X, g: A2 --> X)(using (A2 --> X) is Observable): Boolean = {
      (inr >>> copair(f, g)) =?= g
    }

    /** [*h* ∘ *ι*₁,*h* ∘ *ι*₂] = *h*: a morphism out of a coproduct is determined by its injections. */
    def copairUniqueness[X: Obj](h: S --> X)(using (S --> X) is Observable): Boolean = {
      copair(inl >>> h, inr >>> h) =?= h
    }

    /** If *f* = *f*′ and *g* = *g*′, then [*f*,*g*] = [*f*′,*g*′].
      *
      * @note The premise is not checked: *f*′ and *g*′ must be equal to *f* and *g* by construction.
      */
    def copairCongruence[X: Obj](f: A1 --> X, f2: A1 --> X, g: A2 --> X, g2: A2 --> X)(
      using (S --> X) is Observable
    ): Boolean = {
      copair(f, g) =?= copair(f2, g2)
    }
  }
}

object Coproduct {
  import Category.Discrete2
  import Discrete2.Disc2
  import Product.Discrete2Diagram

  /** The coproducts of two objects of a category **C**. */
  type Of[C <: Category] = Coproduct { val category: C }

  /** The coproduct of *X* and *Y* in a category with colimits of the diagrams of shape **2**. */
  def apply(
    colimits: Colimits.Of[Discrete2Diagram.Into],
    first: colimits.category.Object,
    second: colimits.category.Object,
  ): Of[colimits.category.type] { val summand1: first.type; val summand2: second.type } = {
    FromColimit(colimits.colimit(Discrete2Diagram(colimits.category, first, second)))
  }

  /** The coproduct from a colimit *L* of a diagram (*X*,*Y*) of shape **2**.
    *
    * The coproduct is the apex of *L*, its injections are the legs of *L*, and [*f*,*g*] is the factorization through
    * *L* of the cocone with legs *f* and *g*.
    */
  open class FromColimit(tracked val cocone: Colimit.Of[Discrete2Diagram])
      extends Coproduct(cocone.diagram.category, cocone.diagram.first, cocone.diagram.second, cocone.apex) {
    import category.{Obj, -->}

    def inl: A1 --> S = {
      cocone.leg[0]
    }

    def inr: A2 --> S = {
      cocone.leg[1]
    }

    def copair[X: Obj](f: A1 --> X, g: A2 --> X): S --> X = {
      cocone.factor(CopairCocone(cocone.diagram, category.Object[X])(f, g))
    }
  }

  /** A coproduct *S* as a colimit of the diagram (*A*₁,*A*₂) of shape **2**.
    *
    * The apex of the colimit is *S*, its legs are the injections, and the factorization of a cocone is the copairing of
    * its legs.
    */
  final class AsColimit(tracked val coproduct: Coproduct)
      extends Colimit(Discrete2Diagram(coproduct.category, coproduct.summand1, coproduct.summand2), coproduct.apex) {
    import coproduct.category.-->

    def leg[A: Disc2]: diagram.F[A] --> coproduct.S = {
      A.index match {
        case Disc2.Index.Zero => coproduct.inl
        case Disc2.Index.One  => coproduct.inr
      }
    }

    def factor(cocone: Cocone.Under[diagram.type]): coproduct.S --> cocone.X = {
      coproduct.copair[cocone.X](cocone.leg[0], cocone.leg[1])(using cocone.apex.evidence)
    }
  }

  object AsColimit {

    /** The coproduct *S* as a colimit of the diagram (*A*₁,*A*₂) of shape **2**. */
    type Of[S <: Coproduct] = AsColimit { val coproduct: S }
  }

  /** The cocone with apex *X* under a diagram of shape **2** whose legs are *f* and *g*. */
  final class CopairCocone(
    tracked override val diagram: Functor { val source: Discrete2.type },
    tracked override val apex: diagram.target.Object,
  )(
    f: diagram.target.-->[diagram.F[0], apex.A],
    g: diagram.target.-->[diagram.F[1], apex.A],
  ) extends Cocone(diagram, apex) {
    import diagram.target.-->

    def leg[A: Disc2]: diagram.F[A] --> X = {
      A.index match {
        case Disc2.Index.Zero => f
        case Disc2.Index.One  => g
      }
    }
  }
}

/** A binary coproduct structure on a category **K**.
  *
  * Represents the coproduct bifunctor +: **K** × **K** → **K**, a coproduct *A* + *B* of every two objects, where
  *   - *ι*₁: *A* → *A* + *B* and *ι*₂: *B* → *A* + *B* are the injections
  *   - [*f*,*g*]: *A* + *B* → *X* is the copairing of *f*: *A* → *X* and *g*: *B* → *X*, the unique morphism with
  *     [*f*,*g*] ∘ *ι*₁ = *f* and [*f*,*g*] ∘ *ι*₂ = *g*
  *   - *f* + *g* = [*ι*₁ ∘ *f*,*ι*₂ ∘ *g*] is the coproduct of morphisms
  *
  * The structure at two objects *A* and *B* is a [[Coproduct]] on *A* + *B*.
  */
abstract class Coproducts(tracked override val category: Category) extends Endobifunctor(category) {
  import category.{Obj, Object, -->, >>>}

  private given FIsObj: [A: Obj, B: Obj] => (F[A, B] is Obj) = objects[A, B]

  /** The coproduct of *A* and *B*: a [[Coproduct]] on *A* + *B*, with its injections and copairing. */
  def coproduct[A: Obj, B: Obj]
    : Coproduct.Of[category.type] { val summand1: A is Object; val summand2: B is Object; val apex: F[A, B] is Object }

  /** *f* + *g* = [*ι*₁ ∘ *f*,*ι*₂ ∘ *g*]
    */
  def bimap[A1: Obj, A2: Obj, B1: Obj, B2: Obj](f: A1 --> B1, g: A2 --> B2): F[A1, A2] --> F[B1, B2] = {
    coproduct[A1, A2].copair(f >>> coproduct[B1, B2].inl, g >>> coproduct[B1, B2].inr)
  }

  /** Laws that any `Coproducts` structure must satisfy.
    *
    * The coproduct of every two objects is a coproduct (see [[Coproduct.CoproductLaws]]), and the coproduct of
    * morphisms is the one that the copairing determines.
    */
  object CoproductsLaws {

    /** [*f*,*g*] ∘ *ι*₁ = *f*
      */
    def copairInl[A: Obj, B: Obj, X: Obj](f: A --> X, g: B --> X)(using (A --> X) is Observable): Boolean = {
      coproduct[A, B].CoproductLaws.copairInl(f, g)
    }

    /** [*f*,*g*] ∘ *ι*₂ = *g*
      */
    def copairInr[A: Obj, B: Obj, X: Obj](f: A --> X, g: B --> X)(using (B --> X) is Observable): Boolean = {
      coproduct[A, B].CoproductLaws.copairInr(f, g)
    }

    /** [*h* ∘ *ι*₁,*h* ∘ *ι*₂] = *h*: a morphism out of a coproduct is determined by its injections. */
    def copairUniqueness[A: Obj, B: Obj, X: Obj](h: F[A, B] --> X)(using (F[A, B] --> X) is Observable): Boolean = {
      coproduct[A, B].CoproductLaws.copairUniqueness(h)
    }

    /** If *f* = *f*′ and *g* = *g*′, then [*f*,*g*] = [*f*′,*g*′].
      *
      * @note The premise is not checked: *f*′ and *g*′ must be equal to *f* and *g* by construction.
      */
    def copairCongruence[A: Obj, B: Obj, X: Obj](f: A --> X, f2: A --> X, g: B --> X, g2: B --> X)(
      using (F[A, B] --> X) is Observable
    ): Boolean = {
      coproduct[A, B].CoproductLaws.copairCongruence(f, f2, g, g2)
    }

    /** *f* + *g* = [*ι*₁ ∘ *f*,*ι*₂ ∘ *g*]
      */
    def bimapIsCopairing[A1: Obj, A2: Obj, B1: Obj, B2: Obj](f: A1 --> B1, g: A2 --> B2)(
      using (F[A1, A2] --> F[B1, B2]) is Observable
    ): Boolean = {
      bimap(f, g) =?= coproduct[A1, A2].copair(f >>> coproduct[B1, B2].inl, g >>> coproduct[B1, B2].inr)
    }
  }
}

object Coproducts {
  import Category.Discrete2.Disc2
  import Product.{Components, Discrete2Diagram}

  /** The binary coproduct structures on a category **K**. */
  type On[K <: Category] = Coproducts { val category: K }

  /** The binary coproducts of a category with discrete colimits of shape **2**: the colimits of the diagrams
    * (*A*,*B*).
    */
  def apply(colimits: Colimits.OfDiscrete[Discrete2Diagram.Into])
    : On[colimits.category.type] { type Self[A, B] = colimits.Apex[Disc2, Components[A, B]] } = {
    FromColimits(colimits)
  }

  /** The binary coproducts of discrete colimits *L* of shape **2**.
    *
    * The coproduct *A* + *B* is the apex Apex[**2**,(*A*,*B*)] of the colimit of the diagram (*A*,*B*), a type
    * constructor because the shape is discrete, and its injections and copairing are those of the colimit
    * ([[Coproduct.FromColimit]]).
    */
  open class FromColimits(tracked val colimits: Colimits.OfDiscrete[Discrete2Diagram.Into])
      extends Coproducts(colimits.category) {
    import category.{Obj, Object}

    type Self[A, B] = colimits.Apex[Disc2, Components[A, B]]

    def objects[A: Obj, B: Obj]: F[A, B] is Obj = {
      colimits.colimit(Discrete2Diagram(category, category.Object[A], category.Object[B])).apex.evidence
    }

    def coproduct[A: Obj, B: Obj]
      : Coproduct.Of[category.type] {
        val summand1: A is Object; val summand2: B is Object; val apex: F[A, B] is Object
      } = {
      Coproduct.FromColimit(colimits.colimit(Discrete2Diagram(category, category.Object[A], category.Object[B])))
    }
  }
}
