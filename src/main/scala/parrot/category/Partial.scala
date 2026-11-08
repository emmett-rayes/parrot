package parrot
package category

import scala.annotation.unused

import Category.Type

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

  /** 𝒫 as a promonad over 𝒮: programs, with the functions of 𝒮 as pure arrows.
    *
    * Its category of arrows is 𝒫, and its functor of pure arrows is [[Inclusion]].
    */
  object Computations extends Promonad(Total) {
    type Self = Partial

    def unit[A: Type, B: Type](f: A -> B): A ~> B = {
      fromTotal(f)
    }

    def multiply[A: Type, B: Type, C: Type](g: B ~> C, f: A ~> B): A ~> C = {
      Partial.compose(g, f)
    }
  }

  /** Pairs as a bifunctor on 𝒫: *f* × *g* runs *f*, then *g*. */
  object Tuple2IsBifunctor extends Endobifunctor(Partial) {
    type Self = Tuple2

    def objects[A: Type, B: Type]: (A, B) is Type = {
      Type.TIsType
    }

    def bimap[A1: Type, A2: Type, B1: Type, B2: Type](f: A1 ~> B1, g: A2 ~> B2): (A1, A2) ~> (B1, B2) = {
      (a, b) => (f(a), g(b))
    }

    override def lmap[A: Type, B: Type, C: Type](f: A ~> B): (A, C) ~> (B, C) = {
      (a, c) => (f(a), c)
    }

    override def rmap[A: Type, B: Type, C: Type](g: A ~> B): (C, A) ~> (C, B) = {
      (c, a) => (c, g(a))
    }
  }

  /** The empty type 0 as the terminal object of 𝒫.
    *
    * A program into 0 never returns, so there is exactly one from each type, and ! diverges on every argument. The unit
    * type 1 is not terminal: a program that diverges is a second program into it.
    */
  object NothingIsTerminal extends Terminal(Partial) {
    type Self = Nothing

    def evidence: Nothing is Type = {
      Type.TIsType
    }

    def discard[A: Type]: A ~> Nothing = {
      @annotation.nowarn("msg=Infinite recursive call")
      @annotation.tailrec
      def diverge(a: A): Nothing = {
        diverge(a)
      }
      a => diverge(a)
    }
  }

  /** The empty type 0 as the initial object of 𝒫. */
  object NothingIsInitial extends Initial(Partial) {
    type Self = Nothing

    def evidence: Nothing is Type = {
      Type.TIsType
    }

    def absurd[A: Type]: Nothing ~> A = {
      n => n
    }
  }

  /** Tagged unions as the binary coproducts *A* + *B* of 𝒫. */
  object EitherIsCoproducts extends Coproducts(Partial) {
    type Self = Either

    def objects[A: Type, B: Type]: Either[A, B] is Type = {
      Type.TIsType
    }

    def coproduct[A: Type, B: Type]: EitherIsCoproduct[A, B] = {
      EitherIsCoproduct()
    }

    override def bimap[A1: Type, A2: Type, B1: Type, B2: Type](f: A1 ~> B1, g: A2 ~> B2)
      : Either[A1, A2] ~> Either[B1, B2] = {
      case Left(a)  => Left(f(a))
      case Right(b) => Right(g(b))
    }

    override def lmap[A: Type, B: Type, C: Type](f: A ~> B): Either[A, C] ~> Either[B, C] = {
      case Left(a)  => Left(f(a))
      case Right(c) => Right(c)
    }

    override def rmap[A: Type, B: Type, C: Type](g: A ~> B): Either[C, A] ~> Either[C, B] = {
      case Left(c)  => Left(c)
      case Right(a) => Right(g(a))
    }
  }

  /** The tagged union `Either[A, B]` as the coproduct *A* + *B* of 𝒫. */
  final class EitherIsCoproduct[A, B] extends Coproduct(Partial, Object[A], Object[B]) {
    type Self = Either[A, B]

    def evidence: Either[A, B] is Type = {
      Type.TIsType
    }

    def inl: A ~> Either[A, B] = {
      a => Left(a)
    }

    def inr: B ~> Either[A, B] = {
      b => Right(b)
    }

    def copair[X: Type](f: A ~> X, g: B ~> X): Either[A, B] ~> X = {
      case Left(a)  => f(a)
      case Right(b) => g(b)
    }
  }

  /** Pairs on 𝒫: a symmetric monoidal structure, but not a product. *π*₁ ∘ ⟨*f*,*g*⟩ diverges where *g* does, so it
    * equals *f* only where *g* terminates: the pairs of 𝒫 are its restriction products.
    */
  object Product extends Symmetric(Partial, Object[Unit], Tuple2IsBifunctor) {
    def braid[A: Type, B: Type]: (A, B) ~> (B, A) = {
      (a, b) => (b, a)
    }

    def leftUnitor[A: Type]: (Unit, A) <-> A = {
      Iso(_._2, a => ((), a))
    }

    override def rightUnitor[A: Type]: (A, Unit) <-> A = {
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
    def comonoid[X: Type]: Comonoid.In[Product.type] { type Self = X } = {
      new Comonoid(Product) {
        type Self = X

        def evidence: X is Type = Type.TIsType

        def counit: X ~> Unit = _ => ()

        def comultiply: X ~> (X, X) = x => (x, x)
      }
    }
  }

  /** The coproducts of 𝒫: tagged unions, with the empty type 0 as initial object. */
  object Coproduct extends Cocartesian(Partial, NothingIsInitial, EitherIsCoproducts) {
    override def codiagonal[A: Type]: Either[A, A] ~> A = {
      case Left(a)  => a
      case Right(a) => a
    }
  }

  /** Programs run side by side on pairs: the first component first. */
  object Parallel extends Bistrong.Hom(Programs, Product)

  /** Programs run on one side of a tagged union. */
  object Choice extends Bistrong.Hom(Programs, Coproduct)

  /** Programs run side by side on the products of 𝒮: the first component first. */
  object ComputationsProduct extends Bistrong(Computations, Total.Products) {
    def left[A: Type, B: Type, C: Type]: (A ~> B) -> ((C, A) ~> (C, B)) = {
      p => (c, a) => (c, p(a))
    }
  }

  /** Programs run on one side of a coproduct of 𝒮. */
  object ComputationsCoproduct extends Bistrong(Computations, Total.Coproducts) {
    def left[A: Type, B: Type, C: Type]: (A ~> B) -> (Either[C, A] ~> Either[C, B]) = {
      p => {
        case Left(c)  => Left(c)
        case Right(a) => Right(p(a))
      }
    }
  }

  /** The Kleisli exponentials of 𝒫: program types, with running and currying. */
  object Exponentials extends ClosedFreyd(ComputationsProduct) {
    type Exp[A, B] = A ~> B

    def objects[A: Type, B: Type]: (A ~> B) is Type = {
      Type.TIsType
    }

    def eval[A: Type, B: Type]: (A ~> B, A) ~> B = {
      (p, a) => p(a)
    }

    def curry[A: Type, B: Type, X: Type](p: (X, A) ~> B): X -> (A ~> B) = {
      x => a => p((x, a))
    }
  }

  /** The colimit of a diagram *D*: **J** → 𝒫 of a discrete shape.
    *
    * Represents the colimit (*X*, *ψ*), where
    *   - *X* = Σ_*A* *D*[*A*] is the type of points *x* of *D*[*A*] tagged with *A* ([[Total.Exists]])
    *   - *ψ*_*A*(*x*) = (*A*, *x*)
    *   - [*φ*](*A*, *x*) = *φ*_*A*(*x*)
    *
    * The only morphisms of **J** are identities, so no two points are glued.
    */
  final class DiscreteColimitOf(
    tracked override val diagram: Functor.Into[Partial.type] { val source: Category { type Self <: =:= } },
  ) extends Colimit(diagram, diagram.target.Object[Total.Exists[diagram.source.Obj, diagram.F]]) {
    import diagram.source as J

    def leg[A: J.Obj as obj]: diagram.F[A] ~> X = {
      x => Total.Exists(obj, x)
    }

    def factor(cocone: Cocone.Under[diagram.type]): X ~> cocone.X = {
      s => cocone.leg[s.A](using s.obj).run(s.at)
    }
  }

  /** The colimits of every diagram of a discrete shape in 𝒫.
    *
    * Every diagram with object map *D* on a shape with objects *O* has the colimit given by [[DiscreteColimitOf]].
    */
  object DiscreteColimits extends Colimits.DiscreteInCategory(Partial) {
    type D                     = Functor.Into[Partial.type] { val source: Category { type Self <: =:= } }
    type Apex[O <: Type, D[_]] = Total.Exists[O, D]

    def colimit(functor: D)
      : Colimit.Of[functor.type] { val apex: Apex[functor.source.Obj, functor.F] is functor.target.Object } = {
      DiscreteColimitOf(functor)
    }
  }

  /** 𝒫 is a restriction category, where
    *   - *p̄* = *a* ↦ (*p*(*a*); *a*) runs *p* for its termination only
    *
    * Its total morphisms are exactly those of 𝒮. 𝒫 is not classical: the complement of *p̄* would decide whether *p*
    * terminates.
    */
  object Domains extends Restriction(Partial) {

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

    override def fixFamily[A: Type, B: Type](@unused n: Int)(
      f: (Int -> (A ~> B)) -> Int -> (A ~> B)
    ): Int -> (A ~> B) = {
      lazy val knots: Int -> (A ~> B) = f(i => a => knots(i)(a))
      knots
    }
  }
}
