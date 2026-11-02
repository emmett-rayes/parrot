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
  * 𝒮 is bicartesian closed. See [[Product]], [[Coproduct]], [[Exponential]].
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
  object UnitIsTerminal extends Terminal(Total, Type.TIsType[Unit]) {
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
  }

  /** The pair type (*A*,*B*) as the product *A* × *B* of 𝒮. */
  final class Tuple2IsProduct[A, B] extends Product(Total, Object[A], Object[B], Object[(A, B)]) {
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
  object NothingIsInitial extends Initial(Total, Type.TIsType[Nothing]) {
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
  }

  /** The tagged union `Either[A, B]` as the coproduct *A* + *B* of 𝒮. */
  final class EitherIsCoproduct[A, B] extends Coproduct(Total, Object[A], Object[B], Object[Either[A, B]]) {
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
  object Products extends Cartesian(Total, UnitIsTerminal, Tuple2IsProducts)

  /** The coproducts of 𝒮: tagged unions, with the empty type 0 as initial object. */
  object Coproducts extends Cocartesian(Total, NothingIsInitial, EitherIsCoproducts)

  /** The internal homs of 𝒮: function types, with evaluation and currying. */
  object Exponentials extends Closed(Products) {
    type Exp[A, B] = A -> B

    def objects[A: Type, B: Type]: (A -> B) is Type = {
      Type.TIsType
    }

    def eval[A: Type, B: Type]: ((A -> B, A)) -> B = {
      (f, a) => f(a)
    }

    def curry[A: Type, B: Type, C: Type](f: ((C, A)) -> B): C -> A -> B = {
      c => a => f((c, a))
    }
  }

  /** The limit of a diagram *D*: **J** → 𝒮: the natural families of points of *D*.
    *
    * Represents the limit (*X*, *ψ*), where
    *   - *X* is the type of natural families *x* = (*x*_*A*)_*A*, a point *x*_*A* of *D*[*A*] for each object *A* of
    *     **J**, with *D*(*f*)(*x*_*A*) = *x*_*B* for every *f*: *A* → *B* of **J** ([[LimitOf.Point]])
    *   - *ψ*_*A*(*x*) = *x*_*A*: the leg at *A* picks the point at *A*
    *   - ⟨*φ*⟩(*y*) = (*φ*_*A*(*y*))_*A*: a cone (*Y*, *φ*) factors through the family of its legs at *y*
    *
    * This is the construction of limits from products and equalizers. The families of points are the product
    * ∏_*A* *D*[*A*], which exists in 𝒮 because its objects are types: it is a polymorphic function type. The natural
    * families are a subset of the product, the equalizer of *x* ↦ *x*_*B* and *x* ↦ *D*(*f*)(*x*_*A*), and Scala has
    * no subset types; [[LimitOf.Point]] makes the subset by abstraction (tutorial, §6.5). Neither step looks at the
    * shape of **J**, so this one construction gives every limit of 𝒮.
    */
  final class LimitOf(tracked override val diagram: Functor { val target: Total.type })
      extends Limit(diagram, diagram.target.Object[LimitOf.Point.Of[diagram.type]]) {
    import diagram.source as J
    import LimitOf.Point

    def leg[A: J.Obj]: X -> diagram.F[A] = {
      _.at[A]
    }

    def factor(cone: Cone.Of[diagram.type]): cone.X -> X = {
      y => Point(diagram)([A] => (a: A is J.Obj) ?=> cone.leg[A](using a)(y))
    }
  }

  object LimitOf {

    /** A point of the limit of a diagram *D*: a natural family of points (*x*_*A*)_*A* of *D*, where `at[A]` is
      * *x*_*A*.
      *
      * The type of `at` holds every family, natural or not. The constructor is private to [[LimitOf]], and the only
      * operation that builds points is [[LimitOf.factor]], from the legs of a cone, which are natural by
      * [[Cone.ConeLaws.commutes]]. So every point that exists is natural, and since clients see a point only
      * through the legs, `Point` is, to them, the subset of natural families: by representation independence, as for
      * any abstract type (tutorial, §6.5).
      *
      * @note Naturality is not checked, and cannot be: it quantifies over every morphism of **J**. It holds because
      *   cones are lawful, and it is the cone law of the limit itself, *D*(*f*) ∘ *ψ*_*A* = *ψ*_*B*, at each point.
      */
    final class Point private[LimitOf] (tracked val diagram: Functor { val target: Total.type })(
      val at: [A] -> (A is diagram.source.Obj) ?-> diagram.F[A],
    ) extends caps.Pure

    object Point {

      /** Refines `Point` to a specific diagram *F*. */
      type Of[F <: Functor] = Point { val diagram: F }
    }
  }

  /** The limits of every diagram in 𝒮: every diagram *D*: **J** → 𝒮, of any shape **J**, has the limit
    * [[LimitOf]](*D*).
    */
  object Limits extends Limit.OfDiagram[[K <: Category] =>> Functor { val target: K }](Total) {
    def limit(functor: Functor { val target: Total.type }): Limit.Of[functor.type] = {
      LimitOf(functor)
    }
  }

  /** The limit of a diagram *D*: **J** → 𝒮 of a discrete shape: all families of points of *D*.
    *
    * Represents the limit (*X*, *ψ*), where
    *   - *X* = ∏_*A* *D*[*A*] is the type of families *x* = (*x*_*A*)_*A*, a point *x*_*A* of *D*[*A*] for each object
    *     *A* of **J**
    *   - *ψ*_*A*(*x*) = *x*_*A*: the leg at *A* picks the point at *A*
    *   - ⟨*φ*⟩(*y*) = (*φ*_*A*(*y*))_*A*: a cone (*Y*, *φ*) factors through the family of its legs at *y*
    *
    * The only morphisms of **J** are identities, so every family is natural and the limit is the product itself: unlike
    * [[LimitOf]], it needs no abstraction, and its apex depends only on the objects of *D*.
    */
  final class DiscreteLimitOf(
    tracked override val diagram: Functor {
      val source: Category { type Self[A, B] <: A =:= B }; val target: Total.type
    },
  ) extends Limit(diagram, diagram.target.Object[[A] -> (A is diagram.source.Obj) ?-> diagram.F[A]]) {
    import diagram.source as J

    def leg[A: J.Obj]: X -> diagram.F[A] = {
      x => x[A]
    }

    def factor(cone: Cone.Of[diagram.type]): cone.X -> X = {
      y => [A] => (a: A is J.Obj) ?=> cone.leg[A](using a)(y)
    }
  }

  /** The limits of the diagrams of a discrete shape **J** in 𝒮: the limit of a diagram with object map *F* is
    * [[DiscreteLimitOf]], the type of families Lim[*F*] = ∏_*A* *F*[*A*].
    *
    * @note A method, not a class: the type of the diagrams depends on **J**, and the parent of a class cannot depend on
    *   its parameters.
    */
  def DiscreteLimitsOf(index: Category { type Self[A, B] <: A =:= B })
    : Limit.OfDiscreteDiagram[[K <: Category] =>> Functor { val source: index.type; val target: K }] {
      val category: Total.type
      type Lim[F[_]] = [A] -> (A is index.Obj) ?-> F[A]
    } = {
    new Limit.OfDiscreteDiagram[[K <: Category] =>> Functor { val source: index.type; val target: K }](Total) {
      type Lim[F[_]] = [A] -> (A is index.Obj) ?-> F[A]

      def limit(functor: Functor { val source: index.type; val target: Total.type })
        : Limit.Of[functor.type] { val apex: functor.target.ObjectOf[Lim[functor.F]] } = {
        DiscreteLimitOf(functor)
      }
    }
  }

  /** A point of the sum Σ_*A* *F*[*A*] of a family of types indexed by the objects *A* of a type class *O*: a point of
    * *F*[*A*] at one object *A*, which its type does not show.
    */
  abstract class Sum[O <: Type, F[_]] extends caps.Pure {

    /** The object *A* of the point. */
    type A

    /** Evidence that *A* is an object. */
    def obj: A is O

    /** The point of *F*[*A*]. */
    def at: F[A]
  }

  object Sum {

    /** The point *x* of *F*[*X*] at the object *X*. */
    def apply[O <: Type, F[_], X](o: X is O, x: F[X]): Sum[O, F] = {
      new Sum[O, F] {
        type A = X

        def obj: X is O = o

        def at: F[X] = x
      }
    }
  }

  /** The colimit of a diagram *D*: **J** → 𝒮: the points of *D*, glued along its morphisms.
    *
    * Represents the colimit (*X*, *ψ*), where
    *   - *X* is the type of glued points (*A*, *x*), a point *x* of *D*[*A*] at one object *A* of **J**, with
    *     (*A*, *x*) = (*B*, *D*(*f*)(*x*)) for every *f*: *A* → *B* of **J** ([[ColimitOf.Point]])
    *   - *ψ*_*A*(*x*) = (*A*, *x*): the leg at *A* tags a point with *A*
    *   - [*φ*](*A*, *x*) = *φ*_*A*(*x*): a cocone (*Y*, *φ*) factors through its leg at the object of a point
    *
    * This is the construction of colimits from coproducts and coequalizers. The points at all objects are the sum
    * Σ_*A* *D*[*A*], which exists in 𝒮 because its objects are types: it is an existential type ([[Sum]]). The glued
    * points are a quotient of the sum, the coequalizer of (*f*, *x*) ↦ (*A*, *x*) and (*f*, *x*) ↦ (*B*, *D*(*f*)(*x*)),
    * and Scala has no quotient types; [[ColimitOf.Point]] makes the quotient by abstraction (tutorial, §7.6). Neither
    * step looks at the shape of **J**, so this one construction gives every colimit of 𝒮.
    */
  final class ColimitOf(tracked override val diagram: Functor { val target: Total.type })
      extends Colimit(diagram, diagram.target.Object[ColimitOf.Point.Of[diagram.type]]) {
    import diagram.source as J
    import ColimitOf.Point

    def leg[A: J.Obj as obj]: diagram.F[A] -> X = {
      x => Point(diagram)(Sum(obj, x))
    }

    def factor(cocone: Cocone.Of[diagram.type]): X -> cocone.X = {
      p => cocone.leg[p.sum.A](using p.sum.obj)(p.sum.at)
    }
  }

  object ColimitOf {

    /** A point of the colimit of a diagram *D*: a point of *D* at one object, where `sum` is (*A*, *x*), up to gluing.
      *
      * The representation holds the object of a point, so it tells glued points apart. It is private to [[ColimitOf]],
      * with the constructor: the only operation that builds points is [[ColimitOf.leg]], and the only one that reads
      * them is [[ColimitOf.factor]], through the legs of a cocone, which agree on glued points by
      * [[Cocone.CoconeLaws.commutes]]. So no client can tell glued points apart, and `Point` is, to them, the quotient
      * of the sum by the gluing: by representation independence, as for any abstract type (tutorial, §7.6).
      *
      * @note The gluing is not checked, and cannot be: it quantifies over every morphism of **J**. It holds because
      *   cocones are lawful, and it is the cocone law of the colimit itself, *ψ*_*B* ∘ *D*(*f*) = *ψ*_*A*, at each
      *   point.
      */
    final class Point private[ColimitOf] (tracked val diagram: Functor { val target: Total.type })(
      private[ColimitOf] val sum: Sum[diagram.source.Obj, diagram.F],
    ) extends caps.Pure

    object Point {

      /** Refines `Point` to a specific diagram *F*. */
      type Of[F <: Functor] = Point { val diagram: F }
    }
  }

  /** The colimits of every diagram in 𝒮: every diagram *D*: **J** → 𝒮, of any shape **J**, has the colimit
    * [[ColimitOf]](*D*).
    */
  object Colimits extends Colimit.OfDiagram[[K <: Category] =>> Functor { val target: K }](Total) {
    def colimit(functor: Functor { val target: Total.type }): Colimit.Of[functor.type] = {
      ColimitOf(functor)
    }
  }

  /** The colimit of a diagram *D*: **J** → 𝒮 of a discrete shape: the sum of the points of *D*.
    *
    * Represents the colimit (*X*, *ψ*), where
    *   - *X* = Σ_*A* *D*[*A*] is the type of points of *D*[*A*] at an object *A* of **J** ([[Sum]])
    *   - *ψ*_*A*(*x*) = (*A*, *x*): the leg at *A* tags a point with *A*
    *   - [*φ*](*A*, *x*) = *φ*_*A*(*x*): a cocone (*Y*, *φ*) factors through its leg at the object of a point
    *
    * The only morphisms of **J** are identities, so no two points are glued and the colimit is the sum itself: unlike
    * [[ColimitOf]], it needs no abstraction, and its apex depends only on the objects of *D*.
    */
  final class DiscreteColimitOf(
    tracked override val diagram: Functor {
      val source: Category { type Self[A, B] <: A =:= B }; val target: Total.type
    },
  ) extends Colimit(diagram, diagram.target.Object[Sum[diagram.source.Obj, diagram.F]]) {
    import diagram.source as J

    def leg[A: J.Obj as obj]: diagram.F[A] -> X = {
      x => Sum(obj, x)
    }

    def factor(cocone: Cocone.Of[diagram.type]): X -> cocone.X = {
      s => cocone.leg[s.A](using s.obj)(s.at)
    }
  }

  /** The colimits of the diagrams of a discrete shape **J** in 𝒮: the colimit of a diagram with object map *F* is
    * [[DiscreteColimitOf]], the type of points Colim[*F*] = Σ_*A* *F*[*A*].
    *
    * @note A method, not a class: the type of the diagrams depends on **J**, and the parent of a class cannot depend on
    *   its parameters.
    */
  def DiscreteColimitsOf(index: Category { type Self[A, B] <: A =:= B })
    : Colimit.OfDiscreteDiagram[[K <: Category] =>> Functor { val source: index.type; val target: K }] {
      val category: Total.type
      type Colim[F[_]] = Sum[index.Obj, F]
    } = {
    new Colimit.OfDiscreteDiagram[[K <: Category] =>> Functor { val source: index.type; val target: K }](Total) {
      type Colim[F[_]] = Sum[index.Obj, F]

      def colimit(functor: Functor { val source: index.type; val target: Total.type })
        : Colimit.Of[functor.type] { val apex: functor.target.ObjectOf[Colim[functor.F]] } = {
        DiscreteColimitOf(functor)
      }
    }
  }
}
