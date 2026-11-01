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
  tracked override val U: Terminal.Of[K.type],
  tracked override val T: Products.Of[K.type],
) extends Symmetric(K, U, T) {
  import K.{Iso, Obj, -->, <->, >>>}

  export U.discard
  export T.{fst, snd, pair}

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

  /** Laws that any `Cartesian` structure must satisfy. */
  object CartesianLaws {

    /** *β* = ⟨*π*₂,*π*₁⟩
      */
    def braidIsPairing[A: Obj, B: Obj](using ((A * B) --> (B * A)) is Observable): Boolean = {
      braid[A, B] =?= (snd[A, B] &&& fst[A, B])
    }

    /** *λ* = *π*₂
      */
    def leftUnitorIsSnd[A: Obj](using ((I * A) --> A) is Observable): Boolean = {
      leftUnitor[A].to =?= snd[I, A]
    }

    /** *ρ* = *π*₁
      */
    def rightUnitorIsFst[A: Obj](using ((A * I) --> A) is Observable): Boolean = {
      rightUnitor[A].to =?= fst[A, I]
    }

    /** *α* = ⟨*π*₁ ∘ *π*₁,⟨*π*₂ ∘ *π*₁,*π*₂⟩⟩
      */
    def associatorIsPairing[A: Obj, B: Obj, C: Obj](
      using (((A * B) * C) --> (A * (B * C))) is Observable
    ): Boolean = {
      val pairing = (fst[A * B, C] >>> fst[A, B]) &&& ((fst[A * B, C] >>> snd[A, B]) &&& snd[A * B, C])
      associator[A, B, C].to =?= pairing
    }
  }
}

object Cartesian {

  /** The cocartesian opposite **K**ᵒᵖ of a cartesian category **K**.
    *
    * The products, projections and pairing in **K** become coproducts, injections and copairing in **K**ᵒᵖ.
    */
  final class Op(tracked val C: Cartesian)
      extends Cocartesian(C.K.op, Category.Object(C.K.op, C.U.U), Endobifunctor.Op(C.T)) {
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
