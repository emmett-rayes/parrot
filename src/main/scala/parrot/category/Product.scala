package parrot
package category

/** A product of two objects of a category **C**.
  *
  * Represents a product *P* = *A*₁ × *A*₂, where
  *   - *π*₁: *P* → *A*₁ and *π*₂: *P* → *A*₂ are the projections
  *   - ⟨*f*,*g*⟩: *X* → *P* is the pairing of *f*: *X* → *A*₁ and *g*: *X* → *A*₂, the unique morphism with *π*₁ ∘
  *     ⟨*f*,*g*⟩ = *f* and *π*₂ ∘ ⟨*f*,*g*⟩ = *g*
  */
abstract class Product(tracked val C: Category, tracked val U1: C.Obj, tracked val U2: C.Obj, tracked val U: C.Obj)
    extends caps.Pure {
  import C.{Obj, -->, >>>}

  /** The first factor *A*₁. */
  final type A1 = U1.Self

  /** The second factor *A*₂. */
  final type A2 = U2.Self

  /** The product *P*. */
  final type P = U.Self

  private given A1IsObj: (A1 is Obj) = U1

  private given A2IsObj: (A2 is Obj) = U2

  private given PIsObj: (P is Obj) = U

  /** The first projection *π*₁: *P* → *A*₁. */
  def fst: P --> A1

  /** The second projection *π*₂: *P* → *A*₂. */
  def snd: P --> A2

  /** The pairing ⟨*f*,*g*⟩: *X* → *P* of *f*: *X* → *A*₁ and *g*: *X* → *A*₂. */
  def pair[X: Obj](f: X --> A1, g: X --> A2): X --> P

  /** The product as a limit of the diagram (*A*₁,*A*₂) of shape **2**: its legs are the projections, and the
    * factorization of a cone is the pairing of its legs.
    */
  final lazy val limit: Product.AsLimit { val P: Product.this.type } = Product.AsLimit(this)

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

  /** The products of **K**. */
  type Of[K <: Category] = Product { val C: K }

  /** The product of *X* and *Y* in a category with limits of shape **2**: the limit of the diagram (*X*,*Y*). */
  def apply(L: Limits { val J: Discrete2.type }, X: L.C.Obj, Y: L.C.Obj)
    : Product { val C: L.C.type; val U1: X.type; val U2: Y.type } = {
    FromLimit(L.limit(Discrete2Diagram(L.C, X, Y)))
  }

  /** The product of a limit *L* of a diagram (*X*,*Y*) of shape **2**.
    *
    * The product is the apex of *L*, its projections are the legs of *L*, and ⟨*f*,*g*⟩ is the factorization through
    * *L* of the cone with legs *f* and *g*.
    */
  open class FromLimit(tracked val L: Limit.Of[Discrete2Diagram])
      extends Product(L.D.K, L.D.X, L.D.Y, L.apex) {
    import C.{Obj, -->}

    def fst: P --> A1 = {
      L.leg[0]
    }

    def snd: P --> A2 = {
      L.leg[1]
    }

    def pair[X: Obj as obj](f: X --> A1, g: X --> A2): X --> P = {
      L.factor(PairCone(L.D, obj)(f, g))
    }
  }

  /** A product *P* as a limit of the diagram (*A*₁,*A*₂) of shape **2**.
    *
    * The apex of the limit is *P*, its legs are the projections, and the factorization of a cone is the pairing of its
    * legs.
    */
  final class AsLimit(tracked val P: Product) extends Limit(Discrete2Diagram(P.C, P.U1, P.U2)) {
    import P.C.-->

    type Apex = P.P

    def apex: P.P is P.C.Obj = {
      P.U
    }

    def leg[A: Disc2]: P.P --> D.F[A] = {
      A.index match {
        case Disc2.Index.Zero => P.fst
        case Disc2.Index.One  => P.snd
      }
    }

    def factor(K: Limit.Cone { val D: AsLimit.this.D.type }): K.Apex --> P.P = {
      P.pair[K.Apex](K.leg[0], K.leg[1])(using K.apex)
    }
  }

  /** The cone with apex *Y* over a diagram of shape **2** whose legs are *f* and *g*. */
  final class PairCone(tracked override val D: Functor { val C: Discrete2.type }, tracked val Y: D.D.Obj)(
    f: D.D.-->[Y.Self, D.F[0]],
    g: D.D.-->[Y.Self, D.F[1]],
  ) extends Limit.Cone(D) {
    import D.D.-->

    type Apex = Y.Self

    def apex: Y.Self is D.D.Obj = {
      Y
    }

    def leg[A: Disc2]: Y.Self --> D.F[A] = {
      A.index match {
        case Disc2.Index.Zero => f
        case Disc2.Index.One  => g
      }
    }
  }

  /** The diagram (*X*,*Y*): **2** → **K** of two objects *X* and *Y* of **K**. */
  final class Discrete2Diagram(tracked val K: Category, tracked val X: K.Obj, tracked val Y: K.Obj)
      extends Functor(Discrete2, K) {
    import K.--> as ==>
    import Discrete2.-->

    type Self[A] = A match {
      case 0 => X.Self
      case 1 => Y.Self
    }

    def objects[A: Disc2]: F[A] is K.Obj = {
      A.index match {
        case Disc2.Index.Zero => X
        case Disc2.Index.One  => Y
      }
    }

    def map[A: Disc2, B: Disc2](f: A --> B): F[A] ==> F[B] = {
      f.substituteCo[[T] =>> F[A] ==> F[T]](K.identity[F[A]](using objects[A]))
    }
  }
}
