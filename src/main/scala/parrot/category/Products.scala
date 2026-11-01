package parrot
package category

/** A binary product structure on a category **K**.
  *
  * Represents the product bifunctor ×: **K** × **K** → **K**, a product *A* × *B* of every two objects, where
  *   - *π*₁: *A* × *B* → *A* and *π*₂: *A* × *B* → *B* are the projections
  *   - ⟨*f*,*g*⟩: *X* → *A* × *B* is the pairing of *f*: *X* → *A* and *g*: *X* → *B*, the unique morphism with *π*₁ ∘
  *     ⟨*f*,*g*⟩ = *f* and *π*₂ ∘ ⟨*f*,*g*⟩ = *g*
  *   - *f* × *g* = ⟨*f* ∘ *π*₁,*g* ∘ *π*₂⟩ is the product of morphisms
  */
abstract class Products(tracked override val K: Category) extends Endobifunctor(K) {
  import K.{Obj, -->, >>>}

  /** The first projection *π*₁: *A* × *B* → *A*. */
  def fst[A: Obj, B: Obj]: F[A, B] --> A

  /** The second projection *π*₂: *A* × *B* → *B*. */
  def snd[A: Obj, B: Obj]: F[A, B] --> B

  /** The pairing ⟨*f*,*g*⟩: *X* → *A* × *B* of *f*: *X* → *A* and *g*: *X* → *B*. */
  def pair[X: Obj, A: Obj, B: Obj](f: X --> A, g: X --> B): X --> F[A, B]

  /** *f* × *g* = ⟨*f* ∘ *π*₁,*g* ∘ *π*₂⟩
    */
  def bimap[A1: Obj, A2: Obj, B1: Obj, B2: Obj](f: A1 --> B1, g: A2 --> B2): F[A1, A2] --> F[B1, B2] = {
    pair(fst[A1, A2] >>> f, snd[A1, A2] >>> g)
  }

  /** The product *A* × *B* of two objects, with the projections and pairing at *A* and *B*. */
  final def product[A: Obj as first, B: Obj as second]
    : Products.AsProduct { val T: Products.this.type; val U1: first.type; val U2: second.type } = {
    Products.AsProduct(this, first, second)
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
      bimap(f, g) =?= pair(fst[A1, A2] >>> f, snd[A1, A2] >>> g)
    }
  }
}

object Products {

  /** The binary products of **K**. */
  type Of[K <: Category] = Products { val K: K }

  /** The product *A*₁ × *A*₂ of a binary product structure *T* at two objects *A*₁ and *A*₂.
    *
    * The projections and the pairing are those of *T* at *A*₁ and *A*₂.
    */
  final class AsProduct(tracked val T: Products, tracked override val U1: T.K.Obj, tracked override val U2: T.K.Obj)
      extends Product(T.K, U1, U2, T.objects[U1.Self, U2.Self](using U1, U2)) {
    import C.{Obj, -->}

    def fst: P --> A1 = {
      T.fst[A1, A2]
    }

    def snd: P --> A2 = {
      T.snd[A1, A2]
    }

    def pair[X: Obj](f: X --> A1, g: X --> A2): X --> P = {
      T.pair(f, g)
    }
  }
}
