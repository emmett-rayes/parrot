package parrot
package category

/** A coproduct of two objects of a category **C**.
  *
  * Represents a coproduct *S* = *A*₁ + *A*₂, where
  *   - *ι*₁: *A*₁ → *S* and *ι*₂: *A*₂ → *S* are the injections
  *   - [*f*,*g*]: *S* → *X* is the copairing of *f*: *A*₁ → *X* and *g*: *A*₂ → *X*
  *
  * @see docs/TUTORIAL.md §14.1
  */
abstract class Coproduct(
  tracked override val category: Category,
  tracked val left: category.Object,
  tracked val right: category.Object,
) extends Category.Object(category) {
  import category.{Obj, -->, >>>}

  /** The first summand *A*₁. */
  final type A1 = left.A

  /** The second summand *A*₂. */
  final type A2 = right.A

  /** The coproduct *S* of *A*₁ and *A*₂. */
  final type S = Self

  /** The first injection *ι*₁: *A*₁ → *S*. */
  def inl: A1 --> S

  /** The second injection *ι*₂: *A*₂ → *S*. */
  def inr: A2 --> S

  /** The copairing [*f*,*g*]: *S* → *X* of *f*: *A*₁ → *X* and *g*: *A*₂ → *X*.
    *
    * This is the unique morphism with [*f*,*g*] ∘ *ι*₁ = *f* and [*f*,*g*] ∘ *ι*₂ = *g*.
    */
  def copair[X: Obj](f: A1 --> X, g: A2 --> X): S --> X

  private given A1IsObj: (A1 is Obj) = left.evidence
  private given A2IsObj: (A2 is Obj) = right.evidence
  private given SIsObj: (S is Obj)   = evidence

  /** The coproduct as a colimit of the discrete 2-object diagram, with the injections as legs and the copairing
    * [*f*,*g*] as the factorization of a cocone with legs *f* and *g*.
    */
  final lazy val asColimit: Coproduct.AsColimit.Of[this.type] = Coproduct.AsColimit(this)

  /** The coproduct as a product of **C**ᵒᵖ, with the injections as projections and the copairing as pairing. */
  final lazy val op: Coproduct.Op.Of[this.type] = Coproduct.Op(this)

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

  /** The coproduct of two objects in a category with colimits of the diagrams of shape **2**. */
  def apply(
    colimits: Colimits.OfDiagram[Discrete2Diagram.Into],
    summand1: colimits.category.Object,
    summand2: colimits.category.Object,
  ): Of[colimits.category.type] { val left: summand1.type; val right: summand2.type } = {
    FromColimit(colimits.colimit(Discrete2Diagram(colimits.category, summand1, summand2)))
  }

  /** The coproduct from a colimit *L* of a discrete 2-object diagram.
    *
    * The coproduct is the apex of *L*, its injections are the legs of *L*, and [*f*,*g*]: *S* → *X* is the
    * factorization through *L* of the cocone with apex *X* and legs *f* and *g*.
    */
  open class FromColimit(tracked val colimit: Colimit.Of[Discrete2Diagram])
      extends Coproduct(colimit.diagram.category, colimit.diagram.first, colimit.diagram.second) {
    import category.{Obj, -->}

    type Self = colimit.X

    def evidence: Self is Obj = {
      colimit.apex.evidence
    }

    def inl: A1 --> S = {
      colimit.leg[0]
    }

    def inr: A2 --> S = {
      colimit.leg[1]
    }

    def copair[X: Obj](f: A1 --> X, g: A2 --> X): S --> X = {
      colimit.factor(CopairCocone(colimit.diagram, category.Object[X])(f, g))
    }
  }

  /** A coproduct *S* as a colimit of the discrete 2-object diagram.
    *
    * The apex of the colimit is *S*, its legs are the injections, and the factorization of the cocone with apex *X* and
    * legs *f* and *g* is [*f*,*g*]: *S* → *X*.
    */
  final class AsColimit(tracked val coproduct: Coproduct)
      extends Colimit(Discrete2Diagram(coproduct.category, coproduct.left, coproduct.right), coproduct) {
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

    /** The coproduct *S* as a colimit of the discrete 2-object diagram. */
    type Of[S <: Coproduct] = AsColimit { val coproduct: S }
  }

  /** A coproduct *A*₁ + *A*₂ in a category **C**, as a product of **C**ᵒᵖ.
    *
    * The projections are the injections, and the pairing is the copairing.
    */
  final class Op(tracked val coproduct: Coproduct)
      extends Product(
        coproduct.category.op,
        coproduct.category.op.Object[coproduct.A1](using coproduct.left.evidence),
        coproduct.category.op.Object[coproduct.A2](using coproduct.right.evidence),
      ) {
    import category.{Obj, -->}

    type Self = coproduct.S

    def evidence: Self is Obj = {
      coproduct.evidence
    }

    def fst: P --> A1 = {
      coproduct.inl
    }

    def snd: P --> A2 = {
      coproduct.inr
    }

    def pair[X: Obj](f: X --> A1, g: X --> A2): X --> P = {
      coproduct.copair(f, g)
    }
  }

  object Op {

    /** The coproduct *S* as a product of the opposite category. */
    type Of[S <: Coproduct] = Op { val coproduct: S }
  }

  /** The cocone with apex *X* under a diagram of shape **2**.
    *
    * The copair cocone has legs *f* and *g*.
    */
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

/** A binary coproduct structure on a category **C**.
  *
  * Represents the coproduct bifunctor +: **C** × **C** → **C**, a coproduct *A* + *B* of every two objects.
  */
abstract class Coproducts(tracked override val category: Category) extends Endobifunctor(category) {
  import category.{Obj, Object, -->, >>>}

  /** The coproduct *X* + *Y* is a [[Coproduct]]. */
  def coproduct[X: Obj, Y: Obj]
    : F[X, Y] is Coproduct.Of[category.type] { val left: X is Object; val right: Y is Object }

  private given FIsObj: [A: Obj, B: Obj] => (F[A, B] is Obj) = objects[A, B]

  /** The coproduct *f* + *g*: *A*₁ + *A*₂ → *B*₁ + *B*₂ of *f*: *A*₁ → *B*₁ and *g*: *A*₂ → *B*₂.
    *
    * This is the copairing [*ι*₁ ∘ *f*,*ι*₂ ∘ *g*].
    */
  def bimap[A1: Obj, A2: Obj, B1: Obj, B2: Obj](f: A1 --> B1, g: A2 --> B2): F[A1, A2] --> F[B1, B2] = {
    coproduct[A1, A2].copair(f >>> coproduct[B1, B2].inl, g >>> coproduct[B1, B2].inr)
  }

  /** The opposite bifunctor +ᵒᵖ, as the binary products of **C**ᵒᵖ. */
  override lazy val op: Coproducts.Op.Of[this.type] = Coproducts.Op(this)

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

  /** The binary coproduct structures on a category **C**. */
  type On[C <: Category] = Coproducts { val category: C }

  /** The binary coproducts of a category with discrete colimits of the diagrams of shape **2**. */
  def apply(colimits: Colimits.OfDiscreteDiagram[Discrete2Diagram.Into])
    : On[colimits.category.type] { type Self[A, B] = colimits.Apex[Disc2, Components[A, B]] } = {
    FromColimits(colimits)
  }

  /** The binary coproducts from discrete colimits *L* of the diagrams of shape **2**.
    *
    * The coproduct *A* + *B* is the apex Apex[**2**,(*A*,*B*)] of the colimit of the discrete 2-object diagram.
    */
  open class FromColimits(tracked val colimits: Colimits.OfDiscreteDiagram[Discrete2Diagram.Into])
      extends Coproducts(colimits.category) {
    import category.{Obj, Object}

    type Self[A, B] = colimits.Apex[Disc2, Components[A, B]]

    def objects[A: Obj, B: Obj]: F[A, B] is Obj = {
      colimits.colimit(Discrete2Diagram(category, category.Object[A], category.Object[B])).apex.evidence
    }

    def coproduct[X: Obj, Y: Obj]
      : F[X, Y] is Coproduct.Of[category.type] { val left: X is Object; val right: Y is Object } = {
      Coproduct.FromColimit(colimits.colimit(Discrete2Diagram(category, category.Object[X], category.Object[Y])))
    }
  }

  /** The binary coproducts of a category **C**, as the binary products of **C**ᵒᵖ.
    *
    * The product of two objects is their coproduct, and the product of morphisms is the coproduct of their opposites.
    */
  final class Op(tracked val coproducts: Coproducts) extends Products(coproducts.category.op) {
    import category.{Obj, Object, -->}

    type Self = coproducts.F

    def objects[A: Obj, B: Obj]: F[A, B] is Obj = {
      coproducts.objects[A, B]
    }

    def product[X: Obj, Y: Obj]
      : F[X, Y] is Product.Of[category.type] { val first: X is Object; val second: Y is Object } = {
      coproducts.coproduct[X, Y].op
    }

    override def bimap[A1: Obj, A2: Obj, B1: Obj, B2: Obj](f: A1 --> B1, g: A2 --> B2): F[A1, A2] --> F[B1, B2] = {
      coproducts.bimap(f, g)
    }
  }

  object Op {

    /** The binary coproducts *S* of a category **C**, as the binary products of **C**ᵒᵖ. */
    type Of[S <: Coproducts] = Op { val coproducts: S }
  }
}
