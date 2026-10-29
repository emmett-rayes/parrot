package parrot
package category

import scala.annotation.unused

/** A program from *A* to *B* that may diverge. */
opaque type Partial[A, B] = A -> B

/** Infix alias for [[Partial]]. */
type ~> = Partial

/** The category 𝒫 of pure Scala programs that may diverge.
  *
  * Represents 𝒫, where
  *   - the objects are all types
  *   - 𝒫(*A*,*B*) are the pure Scala programs *A* → *B*
  *   - *id* = *a* ↦ *a*
  *   - *g* ∘ *f* = *a* ↦ *g*(*f*(*a*))
  *
  * The morphisms of 𝒫 are evaluated strictly. Pairs are not products in 𝒫, since a diverging component makes the pair
  * diverge. 𝒫 is cocartesian. See [[Coproduct]].
  *
  * 𝒮 is the subcategory of 𝒫 of total Scala programs. See [[Partial.Inclusion]], [[Partial.fromTotal]],
  * [[Partial.assumeTotal]].
  */
object Partial extends Category {
  type Self = Partial
  type Obj  = Type

  def identity[A: Type]: A ~> A = {
    a => a
  }

  def compose[A: Type, B: Type, C: Type](g: B ~> C, f: A ~> B): A ~> C = {
    a => g(f(a))
  }

  /** Creates a morphism of 𝒫 from a pure Scala program, total or not. */
  def apply[A, B](f: A -> B): A ~> B = {
    f
  }

  /** Creates a morphism of 𝒫 from a morphism of 𝒮.
    *
    * This represents the inclusion functor 𝒮 → 𝒫. See [[Inclusion]].
    */
  def fromTotal[A, B](f: A -> B): A ~> B = {
    f
  }

  /** Promises that *p* terminates on every argument, which makes it a morphism of 𝒮.
    *
    * @note If *p* diverges, every conclusion drawn from the promise is void.
    */
  def assumeTotal[A, B](p: A ~> B): A -> B = {
    p
  }

  extension [A, B](p: A ~> B)
    /** Runs *p* on *a*. This may diverge. */
    final def run(a: A): B = {
      p(a)
    }

  /** The inclusion functor 𝒮 → 𝒫, where
    *   - *F*[*A*] = *A*: the objects stay the same
    *   - *F*(*f*) = *f*: a morphism of 𝒮 is a morphism of 𝒫 that is total
    */
  object Inclusion extends Functor(Total, Partial) {
    type Self[A] = A

    def objects[A: Type]: A is Type = {
      Type.TIsType
    }

    def map[A: Type, B: Type](f: A -> B): A ~> B = {
      fromTotal(f)
    }
  }

  /** 𝒫 as a promonad over itself. */
  object Programs extends Promonad.Hom(Partial)

  /** Pairs as a bifunctor on 𝒫: *f* × *g* runs *f*, then *g*. */
  object Tuple2IsBifunctor extends Bifunctor(Partial, Partial, Partial) {
    type Self = Tuple2

    def objects[A: Type, B: Type]: (A, B) is Type = {
      Type.TIsType
    }

    def bimap[A1: Type, B1: Type, A2: Type, B2: Type](f: A1 ~> A2, g: B1 ~> B2): (A1, B1) ~> (A2, B2) = {
      (a, b) => (f(a), g(b))
    }
  }

  /** Tagged unions as a bifunctor on 𝒫. */
  object EitherIsBifunctor extends Bifunctor(Partial, Partial, Partial) {
    type Self = Either

    def objects[A: Type, B: Type]: Either[A, B] is Type = {
      Type.TIsType
    }

    def bimap[A1: Type, B1: Type, A2: Type, B2: Type](f: A1 ~> A2, g: B1 ~> B2): Either[A1, B1] ~> Either[A2, B2] = {
      case Left(a)  => Left(f(a))
      case Right(b) => Right(g(b))
    }
  }

  /** Pairs on 𝒫: a symmetric monoidal structure, but not a product. *π*₁ ∘ ⟨*f*,*g*⟩ diverges where *g* does, so it
    * equals *f* only where *g* terminates: the pairs of 𝒫 are its restriction products.
    */
  object Product extends Symmetric(Partial, Tuple2IsBifunctor) {
    type I = Unit

    def unitObject: Unit is Type = {
      Type.TIsType
    }

    def braid[A: Type, B: Type]: (A, B) ~> (B, A) = {
      (a, b) => (b, a)
    }

    def leftUnitor[A: Type]: (Unit, A) <-> A = {
      Iso(_._2, a => ((), a))
    }

    def rightUnitor[A: Type]: (A, Unit) <-> A = {
      Iso(_._1, a => (a, ()))
    }

    def associator[A: Type, B: Type, C: Type]: ((A, B), C) <-> (A, (B, C)) = {
      Iso({ case ((a, b), c) => (a, (b, c)) }, { case (a, (b, c)) => ((a, b), c) })
    }

    /** Every type is a comonoid for pairs in 𝒫, by deleting and copying, which are total programs.
      *
      * @note Unlike in a cartesian category, programs need not preserve it: one that does not terminate cannot be
      *   deleted, *p* ⨾ ! ≠ !. By Fox's theorem, this is exactly why the pairs of 𝒫 are not products.
      */
    def comonoid[A: Type]: Comonoid { val V: Product.type; type Self = A } = {
      new Comonoid(Product) {
        type Self = A

        def carrier: A is Type = Type.TIsType

        def counit: A ~> Unit = _ => ()

        def comultiply: A ~> (A, A) = a => (a, a)
      }
    }
  }

  /** The coproducts of 𝒫: tagged unions, with the empty type 0 as initial object. */
  object Coproduct extends Cocartesian(Partial, EitherIsBifunctor) {
    type I = Nothing

    def unitObject: Nothing is Type = {
      Type.TIsType
    }

    def inl[A: Type, B: Type]: A ~> Either[A, B] = {
      a => Left(a)
    }

    def inr[A: Type, B: Type]: B ~> Either[A, B] = {
      b => Right(b)
    }

    def copair[A: Type, B: Type, X: Type](f: A ~> X, g: B ~> X): Either[A, B] ~> X = {
      case Left(a)  => f(a)
      case Right(b) => g(b)
    }

    def absurd[A: Type]: Nothing ~> A = {
      n => n
    }
  }

  /** Programs run side by side on pairs: the first component first. */
  object Parallel extends Strong.OfHom(Programs, Product)

  /** Programs run on one side of a tagged union. */
  object Choice extends Strong.OfHom(Programs, Coproduct)

  /** 𝒫 is a restriction category, where
    *   - *p̄* = *a* ↦ (*p*(*a*); *a*) runs *p* for its termination only
    *
    * Its total morphisms are exactly those of 𝒮. 𝒫 is not classical: the complement of *p̄* would decide whether *p*
    * terminates.
    */
  object Domains extends Restriction(Programs) {

    def restrict[A: Type, B: Type](p: A ~> B): A ~> A = {
      a =>
        val _ = p(a)
        a
    }
  }

  /** Iteration in 𝒫: the while loop, defined for every step, terminating or not. */
  object Loops extends Elgot(Choice) {

    def iterate[A: Type, X: Type](p: X ~> Either[A, X]): X ~> A = {
      @annotation.tailrec
      def loop(x: X): A = {
        p(x) match {
          case Left(a)  => a
          case Right(y) => loop(y)
        }
      }
      x => loop(x)
    }
  }

  /** Feedback in 𝒫 through coproducts: the trace of [[Loops]]. */
  object Feedback extends Traced.OfElgot(Loops)

  /** Recursion in 𝒫 at the types of programs: *fix*(*f*) is the knot *k* = *f*(*a* ↦ *k*(*a*)).
    *
    * The η-expansion *a* ↦ *k*(*a*) delays the recursive reference until the program runs, so building the knot
    * terminates; running it may not. This is why strict languages have fixed points at function types only.
    */
  object Knots extends Recursion(Programs) {

    def fix[A: Type, B: Type](f: (A ~> B) -> (A ~> B)): A ~> B = {
      lazy val knot: A ~> B = f(a => knot(a))
      knot
    }

    def fixFamily[A: Type, B: Type](@unused n: Int)(f: (Int -> (A ~> B)) -> Int -> (A ~> B)): Int -> (A ~> B) = {
      lazy val knots: Int -> (A ~> B) = f(i => a => knots(i)(a))
      knots
    }
  }
}
