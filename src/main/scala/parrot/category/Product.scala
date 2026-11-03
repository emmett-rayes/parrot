package parrot
package category

/** A product of two objects of a category **C**.
  *
  * Represents a product *P* = *A*₁ × *A*₂, where
  *   - *π*₁: *P* → *A*₁ and *π*₂: *P* → *A*₂ are the projections
  *   - ⟨*f*,*g*⟩: *X* → *P* is the pairing of *f*: *X* → *A*₁ and *g*: *X* → *A*₂, the unique morphism with *π*₁ ∘
  *     ⟨*f*,*g*⟩ = *f* and *π*₂ ∘ ⟨*f*,*g*⟩ = *g*
  */
abstract class Product(
  tracked val category: Category,
  tracked val factor1: category.Object,
  tracked val factor2: category.Object,
  tracked val apex: category.Object,
) extends caps.Pure {
  import category.{Obj, -->, >>>}

  /** The first factor *A*₁. */
  final type A1 = factor1.A

  /** The second factor *A*₂. */
  final type A2 = factor2.A

  /** The product *P*. */
  final type P = apex.A

  private given A1IsObj: (A1 is Obj) = factor1.evidence

  private given A2IsObj: (A2 is Obj) = factor2.evidence

  private given PIsObj: (P is Obj) = apex.evidence

  /** The first projection *π*₁: *P* → *A*₁. */
  def fst: P --> A1

  /** The second projection *π*₂: *P* → *A*₂. */
  def snd: P --> A2

  /** The pairing ⟨*f*,*g*⟩: *X* → *P* of *f*: *X* → *A*₁ and *g*: *X* → *A*₂. */
  def pair[X: Obj](f: X --> A1, g: X --> A2): X --> P

  /** The product as a limit of the diagram (*A*₁,*A*₂) of shape **2**: its legs are the projections, and the
    * factorization of a cone is the pairing of its legs.
    */
  final lazy val limit: Product.AsLimit { val product: Product.this.type } = Product.AsLimit(this)

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

  /** The products of the category **K**. */
  type Of[K <: Category] = Product { val category: K }

  /** The product of *X* and *Y* in a category with limits of the diagrams of shape **2**. */
  def apply(limits: Limit.OfDiagram[Discrete2Diagram.Of], first: limits.category.Object, second: limits.category.Object)
    : Of[limits.category.type] { val factor1: first.type; val factor2: second.type } = {
    FromLimit(limits.limit(Discrete2Diagram(limits.category, first, second)))
  }

  /** The product from a limit *L* of a diagram (*X*,*Y*) of shape **2**.
    *
    * The product is the apex of *L*, its projections are the legs of *L*, and ⟨*f*,*g*⟩ is the factorization through
    * *L* of the cone with legs *f* and *g*.
    */
  open class FromLimit(tracked val cone: Limit.Of[Discrete2Diagram])
      extends Product(cone.diagram.category, cone.diagram.first, cone.diagram.second, cone.apex) {
    import category.{Obj, -->}

    def fst: P --> A1 = {
      cone.leg[0]
    }

    def snd: P --> A2 = {
      cone.leg[1]
    }

    def pair[X: Obj](f: X --> A1, g: X --> A2): X --> P = {
      cone.factor(PairCone(cone.diagram, category.Object[X])(f, g))
    }
  }

  /** A product *P* as a limit of the diagram (*A*₁,*A*₂) of shape **2**.
    *
    * The apex of the limit is *P*, its legs are the projections, and the factorization of a cone is the pairing of its
    * legs.
    */
  final class AsLimit(tracked val product: Product)
      extends Limit(Discrete2Diagram(product.category, product.factor1, product.factor2), product.apex) {
    import product.category.-->

    def leg[A: Disc2]: product.P --> diagram.F[A] = {
      A.index match {
        case Disc2.Index.Zero => product.fst
        case Disc2.Index.One  => product.snd
      }
    }

    def factor(cone: Cone.Of[diagram.type]): cone.X --> product.P = {
      product.pair[cone.X](cone.leg[0], cone.leg[1])(using cone.apex.evidence)
    }
  }

  /** The cone with apex *X* over a diagram of shape **2** whose legs are *f* and *g*. */
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

  /** The object map of a diagram (*X*,*Y*) of shape **2**: 0 ↦ *X* and 1 ↦ *Y*. */
  type Components[X, Y] = [A] =>> A match {
    case 0 => X
    case 1 => Y
  }

  /** The diagram (*X*,*Y*): **2** → **K** of two objects *X* and *Y* of **K**. */
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

    /** Refines `Discrete2Diagram` to a specific category **K**. */
    type Of[K <: Category] = Discrete2Diagram { val category: K }
  }
}

/** A binary product structure on a category **K**.
  *
  * Represents the product bifunctor ×: **K** × **K** → **K**, a product *A* × *B* of every two objects, where
  *   - *π*₁: *A* × *B* → *A* and *π*₂: *A* × *B* → *B* are the projections
  *   - ⟨*f*,*g*⟩: *X* → *A* × *B* is the pairing of *f*: *X* → *A* and *g*: *X* → *B*, the unique morphism with *π*₁ ∘
  *     ⟨*f*,*g*⟩ = *f* and *π*₂ ∘ ⟨*f*,*g*⟩ = *g*
  *   - *f* × *g* = ⟨*f* ∘ *π*₁,*g* ∘ *π*₂⟩ is the product of morphisms
  *
  * The structure at two objects *A* and *B* is a [[Product]] on *A* × *B*.
  */
abstract class Products(tracked override val category: Category) extends Endobifunctor(category) {
  import category.{Obj, Object, -->, >>>}

  private given FIsObj: [A: Obj, B: Obj] => (F[A, B] is Obj) = objects[A, B]

  /** The product of *A* and *B*: a [[Product]] on *A* × *B*, with its projections and pairing. */
  def product[A: Obj, B: Obj]
    : Product.Of[category.type] { val factor1: A is Object; val factor2: B is Object; val apex: F[A, B] is Object }

  /** *f* × *g* = ⟨*f* ∘ *π*₁,*g* ∘ *π*₂⟩
    */
  def bimap[A1: Obj, A2: Obj, B1: Obj, B2: Obj](f: A1 --> B1, g: A2 --> B2): F[A1, A2] --> F[B1, B2] = {
    product[B1, B2].pair(product[A1, A2].fst >>> f, product[A1, A2].snd >>> g)
  }

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
  import Category.Discrete2
  import Product.{Components, Discrete2Diagram}

  /** The binary products of **K**. */
  type Of[K <: Category] = Products { val category: K }

  /** The binary products of a category with discrete limits of shape **2**: the limits of the diagrams (*A*,*B*). */
  def apply(limits: Limit.OfDiscreteDiagram[Discrete2Diagram.Of])
    : Of[limits.category.type] { type Self[A, B] = limits.Lim[Components[A, B]] } = {
    FromLimits(limits)
  }

  /** The binary products of discrete limits *L* of shape **2**.
    *
    * The product *A* × *B* is the apex Lim[(*A*,*B*)] of the limit of the diagram (*A*,*B*), a type constructor
    * because the shape is discrete, and its projections and pairing are those of the limit ([[Product.FromLimit]]).
    */
  open class FromLimits(tracked val limits: Limit.OfDiscreteDiagram[Discrete2Diagram.Of])
      extends Products(limits.category) {
    import category.{Obj, Object}

    type Self[A, B] = limits.Lim[Components[A, B]]

    def objects[A: Obj, B: Obj]: F[A, B] is Obj = {
      limits.limit(Discrete2Diagram(category, category.Object[A], category.Object[B])).apex.evidence
    }

    def product[A: Obj, B: Obj]
      : Product.Of[category.type] {
        val factor1: A is Object; val factor2: B is Object; val apex: F[A, B] is Object
      } = {
      Product.FromLimit(limits.limit(Discrete2Diagram(category, category.Object[A], category.Object[B])))
    }
  }
}
