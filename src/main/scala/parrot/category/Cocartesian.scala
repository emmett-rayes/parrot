package parrot
package category

import scala.annotation.targetName

/** A cocartesian monoidal structure on a category **K**: the tensor is the coproduct and the unit is an initial object.
  *
  * Represents a category with finite coproducts, the dual of [[Cartesian]], where
  *   - *A* + *B* is the coproduct, with injections *ι*₁ and *ι*₂
  *   - [*f*,*g*] is the unique morphism with [*f*,*g*] ∘ *ι*₁ = *f* and [*f*,*g*] ∘ *ι*₂ = *g*
  *   - *I* is initial, with the unique morphism ¡: *I* → *A*
  *   - ∇ = [*id*,*id*] merges
  *
  * The unitors, the associator and the braiding are derived from the injections and copairing.
  */
abstract class Cocartesian(
  tracked override val K: Category,
  tracked override val U: K.Obj,
  tracked override val T: Bifunctor { val C1: K.type; val C2: K.type; val D: K.type },
) extends Symmetric(K, U, T) {
  import K.{Obj, -->, <->, >>>}

  /** Infix alias for [[Tensor]]: the coproduct *A* + *B*. */
  final type + = Tensor

  /** The left injection *ι*₁: *A* → *A* + *B*. */
  def inl[A: Obj, B: Obj]: A --> (A + B)

  /** The right injection *ι*₂: *B* → *A* + *B*. */
  def inr[A: Obj, B: Obj]: B --> (A + B)

  /** The copairing [*f*,*g*]: *A* + *B* → *X* of *f*: *A* → *X* and *g*: *B* → *X*. */
  def copair[A: Obj, B: Obj, X: Obj](f: A --> X, g: B --> X): (A + B) --> X

  /** The unique morphism ¡: *I* → *A* out of the initial object. */
  def absurd[A: Obj]: I --> A

  /** The codiagonal ∇ = [*id*,*id*]: *A* + *A* → *A*. */
  final def codiagonal[A: Obj]: (A + A) --> A = {
    copair(K.identity[A], K.identity[A])
  }

  extension [A: Obj, X: Obj](f: A --> X)
    /** Infix form of [[copair]]: [*f*,*g*]. */
    @targetName("copairExt")
    final def |||[B: Obj](g: B --> X): (A + B) --> X = {
      copair(f, g)
    }

  extension [A: Obj, B: Obj](f: A --> B)
    /** Infix form of [[tensor]] for coproducts: *f* + *g*. */
    final def +++[C: Obj, D: Obj](g: C --> D): (A + C) --> (B + D) = {
      tensor(f, g)
    }

  /** *β* = [*ι*₂,*ι*₁]
    */
  def braid[A: Obj, B: Obj]: (A + B) --> (B + A) = {
    copair(inr[B, A], inl[B, A])
  }

  /** *λ* = [¡,*id*], with inverse *ι*₂
    */
  def leftUnitor[A: Obj]: (I + A) <-> A = {
    K.Iso(copair(absurd[A], K.identity[A]), inr[I, A])
  }

  /** *ρ* = [*id*,¡], with inverse *ι*₁
    */
  def rightUnitor[A: Obj]: (A + I) <-> A = {
    K.Iso(copair(K.identity[A], absurd[A]), inl[A, I])
  }

  /** *α* = [[*ι*₁,*ι*₂ ∘ *ι*₁],*ι*₂ ∘ *ι*₂], with the symmetric inverse
    */
  def associator[A: Obj, B: Obj, C: Obj]: ((A + B) + C) <-> (A + (B + C)) = {
    val to   = (inl[A, B + C] ||| (inl[B, C] >>> inr[A, B + C])) ||| (inr[B, C] >>> inr[A, B + C])
    val from = (inl[A, B] >>> inl[A + B, C]) ||| ((inr[A, B] >>> inl[A + B, C]) ||| inr[A + B, C])
    K.Iso(to, from)
  }

  /** Laws that any `Cocartesian` structure must satisfy: the universal property of coproducts and of the initial
    * object.
    */
  object CocartesianLaws {

    /** [*f*,*g*] ∘ *ι*₁ = *f* */
    def copairInl[A: Obj, B: Obj, X: Obj](f: A --> X, g: B --> X)(
      using (A --> X) is Observable
    ): Boolean = {
      (inl[A, B] >>> (f ||| g)) =?= f
    }

    /** [*f*,*g*] ∘ *ι*₂ = *g* */
    def copairInr[A: Obj, B: Obj, X: Obj](f: A --> X, g: B --> X)(
      using (B --> X) is Observable
    ): Boolean = {
      (inr[A, B] >>> (f ||| g)) =?= g
    }

    /** [*h* ∘ *ι*₁,*h* ∘ *ι*₂] = *h*: a morphism out of a coproduct is determined by its injections. */
    def copairUniqueness[A: Obj, B: Obj, X: Obj](h: (A + B) --> X)(
      using ((A + B) --> X) is Observable
    ): Boolean = {
      ((inl[A, B] >>> h) ||| (inr[A, B] >>> h)) =?= h
    }

    /** *f* = ¡ for every *f*: *I* → *A*
      */
    def absurdUniqueness[A: Obj](f: I --> A)(using (I --> A) is Observable): Boolean = {
      f =?= absurd[A]
    }

    /** *f* + *g* = [*ι*₁ ∘ *f*,*ι*₂ ∘ *g*]: the tensor is the coproduct.
      */
    def tensorIsCoproduct[A: Obj, B: Obj, C: Obj, D: Obj](f: A --> B, g: C --> D)(
      using ((A + C) --> (B + D)) is Observable
    ): Boolean = {
      (f +++ g) =?= ((f >>> inl[B, D]) ||| (g >>> inr[B, D]))
    }

    /** If *f* = *f*′ and *g* = *g*′, then [*f*,*g*] = [*f*′,*g*′].
      *
      * @note The premise is not checked: *f*′ and *g*′ must be equal to *f* and *g* by construction.
      */
    def copairCongruence[A: Obj, B: Obj, X: Obj](
      f: A --> X,
      f2: A --> X,
      g: B --> X,
      g2: B --> X,
    )(using ((A + B) --> X) is Observable): Boolean = {
      (f ||| g) =?= (f2 ||| g2)
    }
  }
}

object Cocartesian {

  /** The coproducts of **K**, read in **K**ᵒᵖ: products, with injections as projections and copairing as pairing. */
  final class Op(tracked val C: Cocartesian) extends Cartesian(C.K.op, C.U, Cartesian.Tensor(C)) {
    import K.{Obj, -->}

    def fst[A: Obj, B: Obj]: (A * B) --> A = {
      C.inl[A, B]
    }

    def snd[A: Obj, B: Obj]: (A * B) --> B = {
      C.inr[A, B]
    }

    def pair[X: Obj, A: Obj, B: Obj](f: X --> A, g: X --> B): X --> (A * B) = {
      C.copair(f, g)
    }

    def discard[A: Obj]: A --> I = {
      C.absurd[A]
    }
  }
}
