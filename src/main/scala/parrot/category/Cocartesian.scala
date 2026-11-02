package parrot
package category

import scala.annotation.targetName

/** A cocartesian monoidal structure on a category **K**.
  *
  * Represents a category with finite coproducts, the dual of [[Cartesian]], where
  *   - *A* + *B* is the coproduct, with injections *ι*₁ and *ι*₂
  *   - [*f*,*g*] is the unique morphism with [*f*,*g*] ∘ *ι*₁ = *f* and [*f*,*g*] ∘ *ι*₂ = *g*
  *   - *I* is initial, with the unique morphism ¡: *I* → *A*
  *   - ∇ = [*id*,*id*] merges
  *
  * In a cocartesian category, the tensor is the coproduct and the unit is an initial object. The unitors, the
  * associator and the braiding are derived from the injections and copairing.
  */
abstract class Cocartesian(
  tracked override val category: Category,
  tracked override val unit: Initial.Of[category.type],
  tracked override val tensor: Coproducts.Of[category.type],
) extends Symmetric(category, unit, tensor) {
  import category.{Iso, Obj, -->, <->, >>>}

  export unit.absurd

  /** Infix alias for [[Tensor]]: the coproduct *A* + *B*. */
  final type + = Tensor

  private given IIsObj: (I is Obj) = unit.evidence

  private given TensorIsObj: [A: Obj, B: Obj] => ((A + B) is Obj) = tensor.objects[A, B]

  /** The first injection *ι*₁: *A* → *A* + *B* of the coproduct of *A* and *B*. */
  final def inl[A: Obj, B: Obj]: A --> (A + B) = {
    tensor.coproduct[A, B].inl
  }

  /** The second injection *ι*₂: *B* → *A* + *B* of the coproduct of *A* and *B*. */
  final def inr[A: Obj, B: Obj]: B --> (A + B) = {
    tensor.coproduct[A, B].inr
  }

  /** The copairing [*f*,*g*]: *A* + *B* → *X* of *f*: *A* → *X* and *g*: *B* → *X* in the coproduct of *A* and *B*. */
  final def copair[A: Obj, B: Obj, X: Obj](f: A --> X, g: B --> X): (A + B) --> X = {
    tensor.coproduct[A, B].copair(f, g)
  }

  /** The codiagonal ∇ = [*id*,*id*]: *A* + *A* → *A*. */
  final def codiagonal[A: Obj]: (A + A) --> A = {
    copair(category.identity[A], category.identity[A])
  }

  /** The corresponding cartesian opposite **K**ᵒᵖ. */
  final lazy val op: Cocartesian.Op { val cocartesian: Cocartesian.this.type } = Cocartesian.Op(this)

  extension [A: Obj, X: Obj](f: A --> X)
    /** Infix extension for [[copair]]. */
    @targetName("copairExt")
    final def |||[B: Obj](g: B --> X): (A + B) --> X = {
      copair(f, g)
    }

  extension [A: Obj, B: Obj](f: A --> B)
    /** Infix extension for [[parallel]] on coproducts. */
    final def +++[C: Obj, D: Obj](g: C --> D): (A + C) --> (B + D) = {
      parallel(f, g)
    }

  /** *β* = [*ι*₂,*ι*₁]
    */
  def braid[A: Obj, B: Obj]: (A + B) --> (B + A) = {
    copair(inr[B, A], inl[B, A])
  }

  /** *λ* = [¡,*id*], with inverse *ι*₂
    */
  def leftUnitor[A: Obj]: (I + A) <-> A = {
    Iso(copair(absurd[A], category.identity[A]), inr[I, A])
  }

  /** *ρ* = [*id*,¡], with inverse *ι*₁
    */
  def rightUnitor[A: Obj]: (A + I) <-> A = {
    Iso(copair(category.identity[A], absurd[A]), inl[A, I])
  }

  /** *α* = [[*ι*₁,*ι*₂ ∘ *ι*₁],*ι*₂ ∘ *ι*₂], with the symmetric inverse
    */
  def associator[A: Obj, B: Obj, C: Obj]: ((A + B) + C) <-> (A + (B + C)) = {
    val to   = (inl[A, B + C] ||| (inl[B, C] >>> inr[A, B + C])) ||| (inr[B, C] >>> inr[A, B + C])
    val from = (inl[A, B] >>> inl[A + B, C]) ||| ((inr[A, B] >>> inl[A + B, C]) ||| inr[A + B, C])
    Iso(to, from)
  }

  /** Laws that any `Cocartesian` structure must satisfy. */
  object CocartesianLaws {

    /** *β* = [*ι*₂,*ι*₁]
      */
    def braidIsCopairing[A: Obj, B: Obj](using ((A + B) --> (B + A)) is Observable): Boolean = {
      braid[A, B] =?= (inr[B, A] ||| inl[B, A])
    }

    /** *λ*⁻¹ = *ι*₂
      */
    def leftUnitorInverseIsInr[A: Obj](using (A --> (I + A)) is Observable): Boolean = {
      leftUnitor[A].from =?= inr[I, A]
    }

    /** *ρ*⁻¹ = *ι*₁
      */
    def rightUnitorInverseIsInl[A: Obj](using (A --> (A + I)) is Observable): Boolean = {
      rightUnitor[A].from =?= inl[A, I]
    }

    /** *α* = [[*ι*₁,*ι*₂ ∘ *ι*₁],*ι*₂ ∘ *ι*₂]
      */
    def associatorIsCopairing[A: Obj, B: Obj, C: Obj](
      using (((A + B) + C) --> (A + (B + C))) is Observable
    ): Boolean = {
      val copairing = (inl[A, B + C] ||| (inl[B, C] >>> inr[A, B + C])) ||| (inr[B, C] >>> inr[A, B + C])
      associator[A, B, C].to =?= copairing
    }
  }
}

object Cocartesian {

  /** The cartesian opposite **K**ᵒᵖ of a cocartesian category **K**.
    *
    * The coproducts, injections and copairing in **K** become products, projections and pairing in **K**ᵒᵖ.
    */
  final class Op(tracked val cocartesian: Cocartesian)
      extends Cartesian(cocartesian.category.op, OpTerminal(cocartesian), OpProducts(cocartesian))

  /** The initial object of a cocartesian category **K**, as the terminal object of **K**ᵒᵖ: ! is ¡. */
  final class OpTerminal(tracked val cocartesian: Cocartesian)
      extends Terminal(cocartesian.category.op, cocartesian.unit.evidence) {
    import category.{Obj, -->}

    def discard[A: Obj]: A --> I = {
      cocartesian.absurd[A]
    }
  }

  /** The coproducts of a cocartesian category **K**, as the binary products of **K**ᵒᵖ.
    *
    * The product of two objects is their coproduct, and the product of morphisms is the coproduct of their opposites.
    */
  final class OpProducts(tracked val cocartesian: Cocartesian) extends Products(cocartesian.category.op) {
    import category.{Obj, ObjectOf, -->}

    type Self = cocartesian.Tensor

    def objects[A: Obj, B: Obj]: F[A, B] is Obj = {
      cocartesian.tensor.objects[A, B]
    }

    def product[A: Obj, B: Obj]
      : OpProduct {
        val cocartesian: OpProducts.this.cocartesian.type; val factor1: ObjectOf[A]; val factor2: ObjectOf[B]
      } = {
      OpProduct(cocartesian, category.Object[A], category.Object[B])
    }

    override def bimap[A1: Obj, A2: Obj, B1: Obj, B2: Obj](f: A1 --> B1, g: A2 --> B2): F[A1, A2] --> F[B1, B2] = {
      cocartesian.parallel(f, g)
    }
  }

  /** The coproduct *A*₁ + *A*₂ in a cocartesian category **K**, as a product of **K**ᵒᵖ.
    *
    * The projections are the injections, and the pairing is the copairing.
    */
  final class OpProduct(
    tracked val cocartesian: Cocartesian,
    tracked override val factor1: cocartesian.category.op.Object,
    tracked override val factor2: cocartesian.category.op.Object,
  ) extends Product(
      cocartesian.category.op,
      factor1,
      factor2,
      cocartesian.category.op.Object(
        using cocartesian.tensor.objects[factor1.A, factor2.A](using factor1.evidence, factor2.evidence),
      ),
    ) {
    import category.{Obj, -->}

    private given A1IsObj: (A1 is Obj) = factor1.evidence

    private given A2IsObj: (A2 is Obj) = factor2.evidence

    def fst: P --> A1 = {
      cocartesian.inl[A1, A2]
    }

    def snd: P --> A2 = {
      cocartesian.inr[A1, A2]
    }

    def pair[X: Obj](f: X --> A1, g: X --> A2): X --> P = {
      cocartesian.copair(f, g)
    }
  }
}
