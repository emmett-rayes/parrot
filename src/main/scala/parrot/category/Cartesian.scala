package parrot
package category

import scala.annotation.targetName

/** A cartesian monoidal structure on a category **K**.
  *
  * Represents a category with finite products, where
  *   - *A* ⊗ *B* is the product, with projections *π*₁ and *π*₂
  *   - ⟨*f*,*g*⟩ is the unique morphism with *π*₁ ∘ ⟨*f*,*g*⟩ = *f* and *π*₂ ∘ ⟨*f*,*g*⟩ = *g*
  *   - *I* is terminal, with the unique morphism !: *A* → *I*
  *   - Δ = ⟨*id*,*id*⟩ copies and ! deletes
  *
  * In a cartesian category, the tensor is the categorical product and the unit is a terminal object. The unitors, the
  * associator and the braiding are derived from the projections and pairing.
  */
abstract class Cartesian(
  tracked override val K: Category,
  tracked override val U: K.Obj,
  tracked override val T: Bifunctor { val C1: K.type; val C2: K.type; val D: K.type },
) extends Symmetric(K, U, T) {
  import K.{Iso, Obj, -->, <->, >>>}

  /** The first projection *π*₁: *A* ⊗ *B* → *A*. */
  def fst[A: Obj, B: Obj]: (A * B) --> A

  /** The second projection *π*₂: *A* ⊗ *B* → *B*. */
  def snd[A: Obj, B: Obj]: (A * B) --> B

  /** The pairing ⟨*f*,*g*⟩: *X* → *A* ⊗ *B* of *f*: *X* → *A* and *g*: *X* → *B*. */
  def pair[X: Obj, A: Obj, B: Obj](f: X --> A, g: X --> B): X --> (A * B)

  /** The unique morphism !: *A* → *I* into the terminal object. */
  def discard[A: Obj]: A --> I

  /** The diagonal Δ = ⟨*id*,*id*⟩: *A* → *A* ⊗ *A*. */
  final def diagonal[A: Obj]: A --> (A * A) = {
    pair(K.identity[A], K.identity[A])
  }

  /** Every object is a comonoid in exactly one way: deleting with ! and copying with Δ. */
  final def comonoid[A: Obj]: Comonoid { val V: Cartesian.this.type; type Self = A } = {
    new Comonoid(this) {
      type Self = A

      def carrier: A is Obj = summon[A is Obj]

      def counit: A --> I = discard[A]

      def comultiply: A --> (A * A) = diagonal[A]
    }
  }

  /** The corresponding cocartesian opposite **K**ᵒᵖ. */
  final lazy val op: Cartesian.Op { val C: Cartesian.this.type } = Cartesian.Op(this)

  extension [X: Obj, A: Obj](f: X --> A)
    /** Infix extension for [[pair]]. */
    @targetName("pairExt")
    final def &&&[B: Obj](g: X --> B): X --> (A * B) = {
      pair(f, g)
    }

  /** *β* = ⟨*π*₂,*π*₁⟩
    */
  def braid[A: Obj, B: Obj]: (A * B) --> (B * A) = {
    pair(snd[A, B], fst[A, B])
  }

  /** *λ* = *π*₂, with inverse ⟨!,*id*⟩
    */
  def leftUnitor[A: Obj]: (I * A) <-> A = {
    Iso(snd[I, A], pair(discard[A], K.identity[A]))
  }

  /** *ρ* = *π*₁, with inverse ⟨*id*,!⟩
    */
  def rightUnitor[A: Obj]: (A * I) <-> A = {
    Iso(fst[A, I], pair(K.identity[A], discard[A]))
  }

  /** *α* = ⟨*π*₁ ∘ *π*₁,⟨*π*₂ ∘ *π*₁,*π*₂⟩⟩, with the symmetric inverse
    */
  def associator[A: Obj, B: Obj, C: Obj]: ((A * B) * C) <-> (A * (B * C)) = {
    val to   = (fst[A * B, C] >>> fst[A, B]) &&& ((fst[A * B, C] >>> snd[A, B]) &&& snd[A * B, C])
    val from = (fst[A, B * C] &&& (snd[A, B * C] >>> fst[B, C])) &&& (snd[A, B * C] >>> snd[B, C])
    Iso(to, from)
  }

  /** Laws that any `Cartesian` structure must satisfy.
    *
    * The product and terminal object satisfy the usual universal properties.
    */
  object CartesianLaws {

    /** *π*₁ ∘ ⟨*f*,*g*⟩ = *f*
      */
    def fstPair[X: Obj, A: Obj, B: Obj](f: X --> A, g: X --> B)(
      using (X --> A) is Observable
    ): Boolean = {
      ((f &&& g) >>> fst[A, B]) =?= f
    }

    /** *π*₂ ∘ ⟨*f*,*g*⟩ = *g*
      */
    def sndPair[X: Obj, A: Obj, B: Obj](f: X --> A, g: X --> B)(
      using (X --> B) is Observable
    ): Boolean = {
      ((f &&& g) >>> snd[A, B]) =?= g
    }

    /** ⟨*π*₁ ∘ *h*,*π*₂ ∘ *h*⟩ = *h*: a morphism into a product is determined by its projections. */
    def pairUniqueness[X: Obj, A: Obj, B: Obj](h: X --> (A * B))(
      using (X --> (A * B)) is Observable
    ): Boolean = {
      ((h >>> fst[A, B]) &&& (h >>> snd[A, B])) =?= h
    }

    /** *f* = ! for every *f*: *A* → *I*
      */
    def discardUniqueness[A: Obj](f: A --> I)(using (A --> I) is Observable): Boolean = {
      f =?= discard[A]
    }

    /** *f* ⊗ *g* = ⟨*f* ∘ *π*₁,*g* ∘ *π*₂⟩: the tensor is the product.
      */
    def tensorIsProduct[A: Obj, B: Obj, C: Obj, D: Obj](f: A --> B, g: C --> D)(
      using ((A * C) --> (B * D)) is Observable
    ): Boolean = {
      (f *** g) =?= ((fst[A, C] >>> f) &&& (snd[A, C] >>> g))
    }

    /** If *f* = *f*′ and *g* = *g*′, then ⟨*f*,*g*⟩ = ⟨*f*′,*g*′⟩.
      *
      * @note The premise is not checked: *f*′ and *g*′ must be equal to *f* and *g* by construction.
      */
    def pairCongruence[X: Obj, A: Obj, B: Obj](
      f: X --> A,
      f2: X --> A,
      g: X --> B,
      g2: X --> B,
    )(using (X --> (A * B)) is Observable): Boolean = {
      (f &&& g) =?= (f2 &&& g2)
    }
  }
}

object Cartesian {

  /** The cocartesian opposite **K**ᵒᵖ of a cartesian category **K**.
    *
    * The products, projections and pairing in **K** become coproducts, injections and copairing in **K**ᵒᵖ.
    */
  final class Op(tracked val C: Cartesian) extends Cocartesian(C.K.op, C.U, C.T.op) {
    import K.{Obj, -->}

    def inl[A: Obj, B: Obj]: A --> (A + B) = {
      C.fst[A, B]
    }

    def inr[A: Obj, B: Obj]: B --> (A + B) = {
      C.snd[A, B]
    }

    def copair[A: Obj, B: Obj, X: Obj](f: A --> X, g: B --> X): (A + B) --> X = {
      C.pair(f, g)
    }

    def absurd[A: Obj]: I --> A = {
      C.discard[A]
    }
  }
}
