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
  final class Tuple2IsProduct[A, B] extends Product(Total, Type.TIsType[A], Type.TIsType[B], Type.TIsType[(A, B)]) {
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
  final class EitherIsCoproduct[A, B]
      extends Coproduct(Total, Type.TIsType[A], Type.TIsType[B], Type.TIsType[Either[A, B]]) {
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
    *     **J**, with *D*(*f*)(*x*_*A*) = *x*_*B* for every *f*: *A* → *B* of **J** ([[Point]])
    *   - *ψ*_*A*(*x*) = *x*_*A*: the leg at *A* picks the point at *A*
    *   - ⟨*φ*⟩(*y*) = (*φ*_*A*(*y*))_*A*: a cone (*Y*, *φ*) factors through the family of its legs at *y*
    *
    * This is the construction of limits from products and equalizers. The families of points are the product
    * ∏_*A* *D*[*A*], which exists in 𝒮 because its objects are types: it is a polymorphic function type. The natural
    * families are a subset of the product, the equalizer of *x* ↦ *x*_*B* and *x* ↦ *D*(*f*)(*x*_*A*), and Scala has
    * no subset types; [[Point]] makes the subset by abstraction (tutorial, §6.5). Neither step looks at the shape of
    * **J**, so this one construction gives every limit of 𝒮.
    */
  final class LimitOf(tracked override val D: Functor { val D: Total.type }) extends Limit(D) {
    import D.C as J

    /** A point of the limit: a natural family of points (*x*_*A*)_*A* of the diagram, where `at[A]` is *x*_*A*.
      *
      * The type of `at` holds every family, natural or not. The constructor is private to the limit, and the only
      * operation that builds points is [[factor]], from the legs of a cone, which are natural by
      * [[Cone.ConeLaws.commutes]]. So every point that exists is natural, and since clients see a point only
      * through the legs, `Point` is, to them, the subset of natural families: by representation independence, as for
      * any abstract type (tutorial, §6.5).
      *
      * @note Naturality is not checked, and cannot be: it quantifies over every morphism of **J**. It holds because
      *   cones are lawful, and it is the cone law of the limit itself, *D*(*f*) ∘ *ψ*_*A* = *ψ*_*B*, at each point.
      */
    final class Point private[LimitOf] (val at: [A] -> (A is J.Obj) ?-> D.F[A]) extends caps.Pure

    type Apex = Point

    def apex: Point is Type = {
      Type.TIsType
    }

    def leg[A: J.Obj]: Point -> D.F[A] = {
      _.at[A]
    }

    def factor(K: Cone { val D: LimitOf.this.D.type }): K.Apex -> Point = {
      y => Point([A] => (a: A is J.Obj) ?=> K.leg[A](using a)(y))
    }
  }

  /** The limits of shape **J** in 𝒮: every diagram *D*: **J** → 𝒮 has the limit [[LimitOf]](*D*), so 𝒮 has limits of
    * every shape.
    */
  final class LimitsOf(tracked override val J: Category) extends Limits(J, Total) {
    def limit(D: Functor { val C: J.type; val D: Total.type }): Limit.Of[D.type] = {
      LimitOf(D)
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
    tracked override val D: Functor { val C: Category { type Self[A, B] <: A =:= B }; val D: Total.type },
  ) extends Limit(D) {
    import D.C as J

    type Apex = [A] -> (A is J.Obj) ?-> D.F[A]

    def apex: Apex is Type = {
      Type.TIsType
    }

    def leg[A: J.Obj]: Apex -> D.F[A] = {
      x => x[A]
    }

    def factor(K: Cone { val D: DiscreteLimitOf.this.D.type }): K.Apex -> Apex = {
      y => [A] => (a: A is J.Obj) ?=> K.leg[A](using a)(y)
    }
  }

  /** The limits of a discrete shape **J** in 𝒮: the limit of a diagram with object map *F* is [[DiscreteLimitOf]], the
    * type of families Lim[*F*] = ∏_*A* *F*[*A*].
    */
  final class DiscreteLimitsOf(tracked override val J: Category { type Self[A, B] <: A =:= B })
      extends DiscreteLimits(J, Total) {
    type Lim[F[_]] = [A] -> (A is J.Obj) ?-> F[A]

    def limit(G: Functor { val C: DiscreteLimitsOf.this.J.type; val D: Total.type })
      : Limit.Of[G.type] { type Apex = Lim[G.F] } = {
      DiscreteLimitOf(G)
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

  /** The colimit of a diagram *D*: **J** → 𝒮 of a discrete shape: the sum of the points of *D*.
    *
    * Represents the colimit (*X*, *ψ*), where
    *   - *X* = Σ_*A* *D*[*A*] is the type of points of *D*[*A*] at an object *A* of **J** ([[Sum]])
    *   - *ψ*_*A*(*x*) = (*A*, *x*): the leg at *A* tags a point with *A*
    *   - [*φ*](*A*, *x*) = *φ*_*A*(*x*): a cocone (*Y*, *φ*) factors through its leg at the object of a point
    *
    * The only morphisms of **J** are identities, so no two points are identified and the colimit is the sum itself:
    * its apex depends only on the objects of *D*. A shape with morphisms would need a quotient, which 𝒮 does not have
    * (tutorial, chapter 7).
    */
  final class DiscreteColimitOf(
    tracked override val D: Functor { val C: Category { type Self[A, B] <: A =:= B }; val D: Total.type },
  ) extends Colimit(D) {
    import D.C as J

    type Apex = Sum[J.Obj, D.F]

    def apex: Apex is Type = {
      Type.TIsType
    }

    def leg[A: J.Obj as obj]: D.F[A] -> Apex = {
      x => Sum(obj, x)
    }

    def factor(K: Cocone { val D: DiscreteColimitOf.this.D.type }): Apex -> K.Apex = {
      s => K.leg[s.A](using s.obj)(s.at)
    }
  }

  /** The colimits of a discrete shape **J** in 𝒮: the colimit of a diagram with object map *F* is
    * [[DiscreteColimitOf]], the type of points Colim[*F*] = Σ_*A* *F*[*A*].
    */
  final class DiscreteColimitsOf(tracked override val J: Category { type Self[A, B] <: A =:= B })
      extends DiscreteColimits(J, Total) {
    type Colim[F[_]] = Sum[J.Obj, F]

    def colimit(G: Functor { val C: DiscreteColimitsOf.this.J.type; val D: Total.type })
      : Colimit.Of[G.type] { type Apex = Colim[G.F] } = {
      DiscreteColimitOf(G)
    }
  }
}
