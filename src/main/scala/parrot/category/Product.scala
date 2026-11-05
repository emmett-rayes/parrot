package parrot
package category

/** A product of two objects of a category **C**.
  *
  * Represents a product *P* = *A*₁ × *A*₂, where
  *   - *π*₁: *P* → *A*₁ and *π*₂: *P* → *A*₂ are the projections
  *   - ⟨*f*,*g*⟩: *X* → *P* is the pairing of *f*: *X* → *A*₁ and *g*: *X* → *A*₂
  */
abstract class Product(
  tracked override val category: Category,
  tracked val first: category.Object,
  tracked val second: category.Object,
) extends Category.Object(category) {
  import category.{Obj, -->, >>>}

  /** The first factor *A*₁. */
  final type A1 = first.A

  /** The second factor *A*₂. */
  final type A2 = second.A

  /** The product *P* of *A*₁ and *A*₂. */
  final type P = Self

  /** The first projection *π*₁: *P* → *A*₁. */
  def fst: P --> A1

  /** The second projection *π*₂: *P* → *A*₂. */
  def snd: P --> A2

  /** The pairing ⟨*f*,*g*⟩: *X* → *P* of *f*: *X* → *A*₁ and *g*: *X* → *A*₂.
    *
    * This is the unique morphism with *π*₁ ∘ ⟨*f*,*g*⟩ = *f* and *π*₂ ∘ ⟨*f*,*g*⟩ = *g*.
    */
  def pair[X: Obj](f: X --> A1, g: X --> A2): X --> P

  private given A1IsObj: (A1 is Obj) = first.evidence
  private given A2IsObj: (A2 is Obj) = second.evidence
  private given PIsObj: (P is Obj)   = evidence

  /** The product as a limit of the discrete 2-object diagram, with the projections as legs and the pairing ⟨*f*,*g*⟩ as
    * the factorization of a cone with legs *f* and *g*.
    */
  final lazy val asLimit: Product.AsLimit.Of[this.type] = Product.AsLimit(this)

  /** The product as a coproduct of **C**ᵒᵖ, with the projections as injections and the pairing as copairing. */
  final lazy val op: Product.Op.Of[this.type] = Product.Op(this)

  /** Laws that any `Product` must satisfy. */
  object ProductLaws {

    /** *π*₁ ∘ ⟨*f*,*g*⟩ = *f*
      */
    def fstPair[X: Obj](f: X --> A1, g: X --> A2)(using (X --> A1) is Observable): Boolean = {
      (pair(f, g) >>> fst) =?= f
    }

    /** *π*₂ ∘ ⟨*f*,*g*⟩ = *g*
      */
    def sndPair[X: Obj](f: X --> A1, g: X --> A2)(using (X --> A2) is Observable): Boolean = {
      (pair(f, g) >>> snd) =?= g
    }

    /** ⟨*π*₁ ∘ *h*,*π*₂ ∘ *h*⟩ = *h*: a morphism into a product is determined by its projections. */
    def pairUniqueness[X: Obj](h: X --> P)(using (X --> P) is Observable): Boolean = {
      pair(h >>> fst, h >>> snd) =?= h
    }

    /** If *f* = *f*′ and *g* = *g*′, then ⟨*f*,*g*⟩ = ⟨*f*′,*g*′⟩.
      *
      * @note The premise is not checked: *f*′ and *g*′ must be equal to *f* and *g* by construction.
      */
    def pairCongruence[X: Obj](f: X --> A1, f2: X --> A1, g: X --> A2, g2: X --> A2)(
      using (X --> P) is Observable
    ): Boolean = {
      pair(f, g) =?= pair(f2, g2)
    }
  }
}

object Product {
  import Category.Discrete2
  import Discrete2.Disc2

  /** The products of two objects of a category **C**. */
  type Of[C <: Category] = Product { val category: C }

  /** The product of two objects in a category with limits of the diagrams of shape **2**. */
  def apply(
    limits: Limits.OfDiagram[Discrete2Diagram.Into],
    factor1: limits.category.Object,
    factor2: limits.category.Object,
  ): Of[limits.category.type] { val first: factor1.type; val second: factor2.type } = {
    FromLimit(limits.limit(Discrete2Diagram(limits.category, factor1, factor2)))
  }

  /** The product from a limit *L* of a discrete 2-object diagram.
    *
    * The product is the apex of *L*, its projections are the legs of *L*, and ⟨*f*,*g*⟩: *X* → *P* is the factorization
    * through *L* of the cone with apex *X* and legs *f* and *g*.
    */
  open class FromLimit(tracked val limit: Limit.Of[Discrete2Diagram])
      extends Product(limit.diagram.category, limit.diagram.first, limit.diagram.second) {
    import category.{Obj, -->}

    type Self = limit.X

    def evidence: Self is Obj = {
      limit.apex.evidence
    }

    def fst: P --> A1 = {
      limit.leg[0]
    }

    def snd: P --> A2 = {
      limit.leg[1]
    }

    def pair[X: Obj](f: X --> A1, g: X --> A2): X --> P = {
      limit.factor(PairCone(limit.diagram, category.Object[X])(f, g))
    }
  }

  /** A product *P* as a limit of the discrete 2-object diagram.
    *
    * The apex of the limit is *P*, its legs are the projections, and the factorization of the cone with apex *X* and
    * legs *f* and *g* is ⟨*f*,*g*⟩: *X* → *P*.
    */
  final class AsLimit(tracked val product: Product)
      extends Limit(Discrete2Diagram(product.category, product.first, product.second), product) {
    import product.category.-->

    def leg[A: Disc2]: product.P --> diagram.F[A] = {
      A.index match {
        case Disc2.Index.Zero => product.fst
        case Disc2.Index.One  => product.snd
      }
    }

    def factor(cone: Cone.Over[diagram.type]): cone.X --> product.P = {
      product.pair[cone.X](cone.leg[0], cone.leg[1])(using cone.apex.evidence)
    }
  }

  object AsLimit {

    /** The product *P* as a limit of the discrete 2-object diagram. */
    type Of[P <: Product] = AsLimit { val product: P }
  }

  /** A product *A*₁ × *A*₂ in a category **C**, as a coproduct of **C**ᵒᵖ.
    *
    * The injections are the projections, and the copairing is the pairing.
    */
  final class Op(tracked val product: Product)
      extends Coproduct(
        product.category.op,
        product.category.op.Object[product.A1](using product.first.evidence),
        product.category.op.Object[product.A2](using product.second.evidence),
      ) {
    import category.{Obj, -->}

    type Self = product.P

    def evidence: Self is Obj = {
      product.evidence
    }

    def inl: A1 --> S = {
      product.fst
    }

    def inr: A2 --> S = {
      product.snd
    }

    def copair[X: Obj](f: A1 --> X, g: A2 --> X): S --> X = {
      product.pair(f, g)
    }
  }

  object Op {

    /** The product *P* as a coproduct of the opposite category. */
    type Of[P <: Product] = Op { val product: P }
  }

  /** The cone with apex *X* over a diagram of shape **2**.
    *
    * The pair cone has legs *f* and *g*.
    */
  final class PairCone(
    tracked override val diagram: Functor { val source: Discrete2.type },
    tracked override val apex: diagram.target.Object,
  )(
    f: diagram.target.-->[apex.A, diagram.F[0]],
    g: diagram.target.-->[apex.A, diagram.F[1]],
  ) extends Cone(diagram, apex) {
    import diagram.target.-->

    def leg[A: Disc2]: X --> diagram.F[A] = {
      A.index match {
        case Disc2.Index.Zero => f
        case Disc2.Index.One  => g
      }
    }
  }

  /** The object map of the discrete 2-object diagram (*X*,*Y*): 0 ↦ *X* and 1 ↦ *Y*. */
  type Components[X, Y] = [A] =>> A match {
    case 0 => X
    case 1 => Y
  }

  /** The discrete 2-object diagram (*X*,*Y*): **2** → **C**, the functor out of **2** that maps 0 to an object *X* and
    * 1 to an object *Y* of **C**.
    */
  final class Discrete2Diagram(
    tracked val category: Category,
    tracked val first: category.Object,
    tracked val second: category.Object,
  ) extends Functor(Discrete2, category) {
    import category.--> as ==>
    import Discrete2.-->

    type Self = Components[first.A, second.A]

    def objects[A: Disc2]: F[A] is category.Obj = {
      A.index match {
        case Disc2.Index.Zero => first.evidence
        case Disc2.Index.One  => second.evidence
      }
    }

    def map[A: Disc2, B: Disc2](f: A --> B): F[A] ==> F[B] = {
      f.substituteCo[[T] =>> F[A] ==> F[T]](category.identity[F[A]](using objects[A]))
    }
  }

  object Discrete2Diagram {

    /** The discrete 2-object diagrams into a category **C**. */
    type Into[C <: Category] = Discrete2Diagram { val category: C }
  }
}

/** A binary product structure on a category **C**.
  *
  * Represents the product bifunctor ×: **C** × **C** → **C**, a product *A* × *B* of every two objects.
  */
abstract class Products(tracked override val category: Category) extends Endobifunctor(category) {
  import category.{Obj, Object, -->, >>>}

  /** The product *X* × *Y* is a [[Product]]. */
  def product[X: Obj, Y: Obj]: F[X, Y] is Product.Of[category.type] { val first: X is Object; val second: Y is Object }

  private given FIsObj: [A: Obj, B: Obj] => (F[A, B] is Obj) = objects[A, B]

  /** The product *f* × *g*: *A*₁ × *A*₂ → *B*₁ × *B*₂ of *f*: *A*₁ → *B*₁ and *g*: *A*₂ → *B*₂.
    *
    * This is the pairing ⟨*f* ∘ *π*₁,*g* ∘ *π*₂⟩.
    */
  def bimap[A1: Obj, A2: Obj, B1: Obj, B2: Obj](f: A1 --> B1, g: A2 --> B2): F[A1, A2] --> F[B1, B2] = {
    product[B1, B2].pair(product[A1, A2].fst >>> f, product[A1, A2].snd >>> g)
  }

  /** The opposite bifunctor ×ᵒᵖ, as the binary coproducts of **C**ᵒᵖ. */
  override lazy val op: Products.Op.Of[this.type] = Products.Op(this)

  /** Laws that any `Products` structure must satisfy.
    *
    * The product of every two objects is a product (see [[Product.ProductLaws]]), and the product of morphisms is the
    * one that the pairing determines.
    */
  object ProductsLaws {

    /** *π*₁ ∘ ⟨*f*,*g*⟩ = *f*
      */
    def fstPair[X: Obj, A: Obj, B: Obj](f: X --> A, g: X --> B)(using (X --> A) is Observable): Boolean = {
      product[A, B].ProductLaws.fstPair(f, g)
    }

    /** *π*₂ ∘ ⟨*f*,*g*⟩ = *g*
      */
    def sndPair[X: Obj, A: Obj, B: Obj](f: X --> A, g: X --> B)(using (X --> B) is Observable): Boolean = {
      product[A, B].ProductLaws.sndPair(f, g)
    }

    /** ⟨*π*₁ ∘ *h*,*π*₂ ∘ *h*⟩ = *h*: a morphism into a product is determined by its projections. */
    def pairUniqueness[X: Obj, A: Obj, B: Obj](h: X --> F[A, B])(using (X --> F[A, B]) is Observable): Boolean = {
      product[A, B].ProductLaws.pairUniqueness(h)
    }

    /** If *f* = *f*′ and *g* = *g*′, then ⟨*f*,*g*⟩ = ⟨*f*′,*g*′⟩.
      *
      * @note The premise is not checked: *f*′ and *g*′ must be equal to *f* and *g* by construction.
      */
    def pairCongruence[X: Obj, A: Obj, B: Obj](f: X --> A, f2: X --> A, g: X --> B, g2: X --> B)(
      using (X --> F[A, B]) is Observable
    ): Boolean = {
      product[A, B].ProductLaws.pairCongruence(f, f2, g, g2)
    }

    /** *f* × *g* = ⟨*f* ∘ *π*₁,*g* ∘ *π*₂⟩
      */
    def bimapIsPairing[A1: Obj, A2: Obj, B1: Obj, B2: Obj](f: A1 --> B1, g: A2 --> B2)(
      using (F[A1, A2] --> F[B1, B2]) is Observable
    ): Boolean = {
      bimap(f, g) =?= product[B1, B2].pair(product[A1, A2].fst >>> f, product[A1, A2].snd >>> g)
    }
  }
}

object Products {
  import Category.Discrete2.Disc2
  import Product.{Components, Discrete2Diagram}

  /** The binary product structures on a category **C**. */
  type On[C <: Category] = Products { val category: C }

  /** The binary products of a category with discrete limits of the diagrams of shape **2**. */
  def apply(limits: Limits.OfDiscreteDiagram[Discrete2Diagram.Into])
    : On[limits.category.type] { type Self[A, B] = limits.Apex[Disc2, Components[A, B]] } = {
    FromLimits(limits)
  }

  /** The binary products from discrete limits *L* of the diagrams of shape **2**.
    *
    * The product *A* × *B* is the apex Apex[**2**,(*A*,*B*)] of the limit of the discrete 2-object diagram.
    */
  open class FromLimits(tracked val limits: Limits.OfDiscreteDiagram[Discrete2Diagram.Into])
      extends Products(limits.category) {
    import category.{Obj, Object}

    type Self[A, B] = limits.Apex[Disc2, Components[A, B]]

    def objects[A: Obj, B: Obj]: F[A, B] is Obj = {
      limits.limit(Discrete2Diagram(category, category.Object[A], category.Object[B])).apex.evidence
    }

    def product[X: Obj, Y: Obj]
      : F[X, Y] is Product.Of[category.type] { val first: X is Object; val second: Y is Object } = {
      Product.FromLimit(limits.limit(Discrete2Diagram(category, category.Object[X], category.Object[Y])))
    }
  }

  /** The binary products of a category **C**, as the binary coproducts of **C**ᵒᵖ.
    *
    * The coproduct of two objects is their product, and the coproduct of morphisms is the product of their opposites.
    */
  final class Op(tracked val products: Products) extends Coproducts(products.category.op) {
    import category.{Obj, Object, -->}

    type Self = products.F

    def objects[A: Obj, B: Obj]: F[A, B] is Obj = {
      products.objects[A, B]
    }

    def coproduct[X: Obj, Y: Obj]
      : F[X, Y] is Coproduct.Of[category.type] { val left: X is Object; val right: Y is Object } = {
      products.product[X, Y].op
    }

    override def bimap[A1: Obj, A2: Obj, B1: Obj, B2: Obj](f: A1 --> B1, g: A2 --> B2): F[A1, A2] --> F[B1, B2] = {
      products.bimap(f, g)
    }
  }

  object Op {

    /** The binary products *P* of a category **C**, as the binary coproducts of **C**ᵒᵖ. */
    type Of[P <: Products] = Op { val products: P }
  }
}
