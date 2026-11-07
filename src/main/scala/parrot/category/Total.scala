package parrot
package category

import Category.Type

/** The category 𝒮 of total, pure Scala programs.
  *
  * Represents 𝒮, where
  *   - the objects are all types
  *   - 𝒮(*A*,*B*) are the total, pure functions *A* → *B*
  *   - *id* = *a* ↦ *a*
  *   - *g* ∘ *f* = *a* ↦ *g*(*f*(*a*))
  *
  * 𝒮 is bicartesian closed. See [[Products]], [[Coproducts]], [[Exponentials]].
  *
  * @note Capture checking makes functions pure. Totality is promised by the user. A function that may diverge belongs
  *   to 𝒫 instead. See [[Partial]].
  */
object Total extends Category {
  type Self[A, B] = A -> B
  type Obj        = Type

  def identity[A: Type]: A -> A = {
    a => a
  }

  def compose[A: Type, B: Type, C: Type](g: B -> C, f: A -> B): A -> C = {
    a => g(f(a))
  }

  /** The identity endofunctor on 𝒮, where
    *   - *F*[*A*] = *A*
    *   - *F*(*f*) = *f*
    */
  object Identity extends Endofunctor(Total) {
    type Self[A] = A

    def objects[A: Type]: A is Type = {
      Type.TIsType
    }

    def map[A: Type, B: Type](f: A -> B): A -> B = {
      f
    }
  }

  /** 𝒮 as a promonad over itself. */
  object Functions extends Promonad.Hom(Total)

  /** The unit type 1 as the terminal object of 𝒮. */
  object UnitIsTerminal extends Terminal(Total) {
    type Self = Unit

    def evidence: Unit is Type = {
      Type.TIsType
    }

    def discard[A: Type]: A -> Unit = {
      _ => ()
    }
  }

  /** Pairs as the binary products *A* × *B* of 𝒮. */
  object Tuple2IsProducts extends Products(Total) {
    type Self = Tuple2

    def objects[A: Type, B: Type]: (A, B) is Type = {
      Type.TIsType
    }

    def product[A: Type, B: Type]: Tuple2IsProduct[A, B] = {
      Tuple2IsProduct()
    }

    override def bimap[A1: Type, A2: Type, B1: Type, B2: Type](f: A1 -> B1, g: A2 -> B2): ((A1, A2)) -> (B1, B2) = {
      (a, b) => (f(a), g(b))
    }

    override def lmap[A: Type, B: Type, C: Type](f: A -> B): ((A, C)) -> (B, C) = {
      (a, c) => (f(a), c)
    }

    override def rmap[A: Type, B: Type, C: Type](g: A -> B): ((C, A)) -> (C, B) = {
      (c, a) => (c, g(a))
    }
  }

  /** The pair type (*A*,*B*) as the product *A* × *B* of 𝒮. */
  final class Tuple2IsProduct[A, B] extends Product(Total, Object[A], Object[B]) {
    type Self = (A, B)

    def evidence: (A, B) is Type = {
      Type.TIsType
    }

    def fst: ((A, B)) -> A = {
      _._1
    }

    def snd: ((A, B)) -> B = {
      _._2
    }

    def pair[X: Type](f: X -> A, g: X -> B): X -> (A, B) = {
      x => (f(x), g(x))
    }
  }

  /** The empty type 0 as the initial object of 𝒮. */
  object NothingIsInitial extends Initial(Total) {
    type Self = Nothing

    def evidence: Nothing is Type = {
      Type.TIsType
    }

    def absurd[A: Type]: Nothing -> A = {
      n => n
    }
  }

  /** Tagged unions as the binary coproducts *A* + *B* of 𝒮. */
  object EitherIsCoproducts extends Coproducts(Total) {
    type Self = Either

    def objects[A: Type, B: Type]: Either[A, B] is Type = {
      Type.TIsType
    }

    def coproduct[A: Type, B: Type]: EitherIsCoproduct[A, B] = {
      EitherIsCoproduct()
    }

    override def bimap[A1: Type, A2: Type, B1: Type, B2: Type](f: A1 -> B1, g: A2 -> B2)
      : Either[A1, A2] -> Either[B1, B2] = {
      case Left(a)  => Left(f(a))
      case Right(b) => Right(g(b))
    }

    override def lmap[A: Type, B: Type, C: Type](f: A -> B): Either[A, C] -> Either[B, C] = {
      case Left(a)  => Left(f(a))
      case Right(c) => Right(c)
    }

    override def rmap[A: Type, B: Type, C: Type](g: A -> B): Either[C, A] -> Either[C, B] = {
      case Left(c)  => Left(c)
      case Right(a) => Right(g(a))
    }
  }

  /** The tagged union `Either[A, B]` as the coproduct *A* + *B* of 𝒮. */
  final class EitherIsCoproduct[A, B] extends Coproduct(Total, Object[A], Object[B]) {
    type Self = Either[A, B]

    def evidence: Either[A, B] is Type = {
      Type.TIsType
    }

    def inl: A -> Either[A, B] = {
      a => Left(a)
    }

    def inr: B -> Either[A, B] = {
      b => Right(b)
    }

    def copair[X: Type](f: A -> X, g: B -> X): Either[A, B] -> X = {
      case Left(a)  => f(a)
      case Right(b) => g(b)
    }
  }

  /** The products of 𝒮: pairs, with the unit type 1 as terminal object. */
  object Products extends Cartesian(Total, UnitIsTerminal, Tuple2IsProducts) {
    override def diagonal[A: Type]: A -> (A, A) = {
      a => (a, a)
    }
  }

  /** The coproducts of 𝒮: tagged unions, with the empty type 0 as initial object. */
  object Coproducts extends Cocartesian(Total, NothingIsInitial, EitherIsCoproducts) {
    override def codiagonal[A: Type]: Either[A, A] -> A = {
      case Left(a)  => a
      case Right(a) => a
    }
  }

  /** The internal homs of 𝒮: function types, with evaluation and currying. */
  object Exponentials extends Closed(Products) {
    type Exp[A, B] = A -> B

    def objects[A: Type, B: Type]: (A -> B) is Type = {
      Type.TIsType
    }

    def eval[A: Type, B: Type]: ((A -> B, A)) -> B = {
      (f, a) => f(a)
    }

    def curry[A: Type, B: Type, X: Type](f: ((X, A)) -> B): X -> A -> B = {
      x => a => f((x, a))
    }

    override def uncurry[A: Type, B: Type, X: Type](g: X -> A -> B): ((X, A)) -> B = {
      (x, a) => g(x)(a)
    }
  }

  /** The limit of a diagram *D*: **J** → 𝒮.
    *
    * Represents the limit (*X*, *ψ*), where
    *   - *X* is the type of natural families *x* = (*x*_*A*)_*A* of points *x*_*A* of *D*[*A*]
    *   - *ψ*_*A*(*x*) = *x*_*A*
    *   - ⟨*φ*⟩(*y*) = (*φ*_*A*(*y*))_*A*
    */
  final class LimitOf(tracked override val diagram: Functor.Into[Total.type])
      extends Limit(diagram, diagram.target.Object[LimitOf.Point.Of[diagram.type]]) {
    import diagram.source as J
    import LimitOf.Point

    def leg[A: J.Obj]: X -> diagram.F[A] = {
      _.at[A]
    }

    def factor(cone: Cone.Over[diagram.type]): cone.X -> X = {
      y => Point(diagram)([A] => (a: A is J.Obj) ?=> cone.leg[A](using a)(y))
    }
  }

  object LimitOf {

    /** A point of the limit of a diagram *D*.
      *
      * `at[A]` is the point at *A*. Only [[LimitOf.factor]] builds points, from the legs of a lawful cone, so every
      * point is a natural family.
      */
    final class Point private[LimitOf] (tracked val diagram: Functor.Into[Total.type])(
      val at: [A] -> (A is diagram.source.Obj) ?-> diagram.F[A],
    ) extends caps.Pure

    object Point {

      /** The points of the limit of a diagram *D*. */
      type Of[D <: Functor] = Point { val diagram: D }
    }
  }

  /** The limits of every diagram in 𝒮.
    *
    * Every diagram *D*: **J** → 𝒮, of any shape **J**, has the limit given by [[LimitOf]].
    */
  object Limits extends category.Limits.InCategory(Total) {
    type D = Functor.Into[Total.type]

    def limit(diagram: D): Limit.Of[diagram.type] = {
      LimitOf(diagram)
    }
  }

  /** The limit of a diagram *D*: **J** → 𝒮 of a discrete shape.
    *
    * Represents the limit (*X*, *ψ*), where
    *   - *X* = ∏_*A* *D*[*A*] is the type of families *x* = (*x*_*A*)_*A* of points *x*_*A* of *D*[*A*]
    *   - *ψ*_*A*(*x*) = *x*_*A*
    *   - ⟨*φ*⟩(*y*) = (*φ*_*A*(*y*))_*A*
    *
    * The only morphisms of **J** are identities, so every family is natural.
    */
  final class DiscreteLimitOf(
    tracked override val diagram: Functor.Into[Total.type] { val source: Category { type Self <: =:= } },
  ) extends Limit(diagram, diagram.target.Object[[A] -> (A is diagram.source.Obj) ?-> diagram.F[A]]) {
    import diagram.source as J

    def leg[A: J.Obj]: X -> diagram.F[A] = {
      x => x[A]
    }

    def factor(cone: Cone.Over[diagram.type]): cone.X -> X = {
      y => [A] => (a: A is J.Obj) ?=> cone.leg[A](using a)(y)
    }
  }

  /** The limits of every diagram of a discrete shape in 𝒮.
    *
    * Every diagram with object map *D* on a shape with objects *O* has the limit given by [[DiscreteLimitOf]].
    */
  object DiscreteLimits extends category.Limits.DiscreteInCategory(Total) {
    type D                     = Functor.Into[Total.type] { val source: Category { type Self <: =:= } }
    type Apex[O <: Type, D[_]] = [A] -> (A is O) ?-> D[A]

    def limit(functor: D)
      : Limit.Of[functor.type] { val apex: Apex[functor.source.Obj, functor.F] is functor.target.Object } = {
      DiscreteLimitOf(functor)
    }
  }

  /** A point of the sum Σ_*A* *F*[*A*] over the objects *A* of a type class *O*.
    *
    * This models existential types.
    */
  abstract class Exists[O <: Type, F[_]] extends caps.Pure {

    /** The object *A* of the point. */
    type A

    /** Evidence that *A* is an object. */
    def obj: A is O

    /** The point of *F*[*A*]. */
    def at: F[A]
  }

  object Exists {

    /** The point *x* of *F*[*X*] at the object *X*. */
    def apply[O <: Type, F[_], X](o: X is O, x: F[X]): Exists[O, F] = {
      new Exists[O, F] {
        type A = X

        def obj: X is O = o

        def at: F[X] = x
      }
    }
  }

  /** The colimit of a diagram *D*: **J** → 𝒮.
    *
    * Represents the colimit (*X*, *ψ*), where
    *   - *X* is the type of points *x* of *D*[*A*] tagged with *A*, with (*A*, *x*) = (*B*, *D*(*f*)(*x*)) for
    *     *f*: *A* → *B*
    *   - *ψ*_*A*(*x*) = (*A*, *x*)
    *   - [*φ*](*A*, *x*) = *φ*_*A*(*x*)
    */
  final class ColimitOf(tracked override val diagram: Functor.Into[Total.type])
      extends Colimit(diagram, diagram.target.Object[ColimitOf.Point.Of[diagram.type]]) {
    import diagram.source as J
    import ColimitOf.Point

    def leg[A: J.Obj as obj]: diagram.F[A] -> X = {
      x => Point(diagram)(Exists(obj, x))
    }

    def factor(cocone: Cocone.Under[diagram.type]): X -> cocone.X = {
      p => cocone.leg[p.sum.A](using p.sum.obj)(p.sum.at)
    }
  }

  object ColimitOf {

    /** A point of the colimit of a diagram *D*.
      *
      * Only [[ColimitOf.factor]] reads points, through the legs of a lawful cocone, so no client can tell glued points
      * apart.
      */
    final class Point private[ColimitOf] (tracked val diagram: Functor.Into[Total.type])(
      private[ColimitOf] val sum: Exists[diagram.source.Obj, diagram.F],
    ) extends caps.Pure

    object Point {

      /** The points of the colimit of a diagram *D*. */
      type Of[D <: Functor] = Point { val diagram: D }
    }
  }

  /** The colimits of every diagram in 𝒮.
    *
    * Every diagram *D*: **J** → 𝒮, of any shape **J**, has the colimit given by [[ColimitOf]].
    */
  object Colimits extends category.Colimits.InCategory(Total) {
    type D = Functor.Into[Total.type]

    def colimit(diagram: D): Colimit.Of[diagram.type] = {
      ColimitOf(diagram)
    }
  }

  /** The colimit of a diagram *D*: **J** → 𝒮 of a discrete shape.
    *
    * Represents the colimit (*X*, *ψ*), where
    *   - *X* = Σ_*A* *D*[*A*] is the type of points *x* of *D*[*A*] tagged with *A* ([[Exists]])
    *   - *ψ*_*A*(*x*) = (*A*, *x*)
    *   - [*φ*](*A*, *x*) = *φ*_*A*(*x*)
    *
    * The only morphisms of **J** are identities, so no two points are glued.
    */
  final class DiscreteColimitOf(
    tracked override val diagram: Functor.Into[Total.type] { val source: Category { type Self <: =:= } },
  ) extends Colimit(diagram, diagram.target.Object[Exists[diagram.source.Obj, diagram.F]]) {
    import diagram.source as J

    def leg[A: J.Obj as obj]: diagram.F[A] -> X = {
      x => Exists(obj, x)
    }

    def factor(cocone: Cocone.Under[diagram.type]): X -> cocone.X = {
      s => cocone.leg[s.A](using s.obj)(s.at)
    }
  }

  /** The colimits of every diagram of a discrete shape in 𝒮.
    *
    * Every diagram with object map *D* on a shape with objects *O* has the colimit given by [[DiscreteColimitOf]].
    */
  object DiscreteColimits extends category.Colimits.DiscreteInCategory(Total) {
    type D                     = Functor.Into[Total.type] { val source: Category { type Self <: =:= } }
    type Apex[O <: Type, D[_]] = Exists[O, D]

    def colimit(functor: D)
      : Colimit.Of[functor.type] { val apex: Apex[functor.source.Obj, functor.F] is functor.target.Object } = {
      DiscreteColimitOf(functor)
    }
  }
}
