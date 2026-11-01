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

  /** Pairs as a bifunctor *A* × *B* on 𝒮. */
  object Tuple2IsBifunctor extends Bifunctor(Total, Total, Total) {
    type Self = Tuple2

    def objects[A: Type, B: Type]: (A, B) is Type = {
      Type.TIsType
    }

    def bimap[A1: Type, A2: Type, B1: Type, B2: Type](f: A1 -> B1, g: A2 -> B2): ((A1, A2)) -> (B1, B2) = {
      (a, b) => (f(a), g(b))
    }
  }

  /** Tagged unions as a bifunctor *A* + *B* on 𝒮. */
  object EitherIsBifunctor extends Bifunctor(Total, Total, Total) {
    type Self = Either

    def objects[A: Type, B: Type]: Either[A, B] is Type = {
      Type.TIsType
    }

    def bimap[A1: Type, A2: Type, B1: Type, B2: Type](f: A1 -> B1, g: A2 -> B2): Either[A1, A2] -> Either[B1, B2] = {
      case Left(a)  => Left(f(a))
      case Right(b) => Right(g(b))
    }
  }

  /** The products of 𝒮: pairs, with the unit type 1 as terminal object. */
  object Product extends Cartesian(Total, Type.TIsType[Unit], Tuple2IsBifunctor) {
    def fst[A: Type, B: Type]: ((A, B)) -> A = {
      _._1
    }

    def snd[A: Type, B: Type]: ((A, B)) -> B = {
      _._2
    }

    def pair[X: Type, A: Type, B: Type](f: X -> A, g: X -> B): X -> (A, B) = {
      x => (f(x), g(x))
    }

    def discard[A: Type]: A -> Unit = {
      _ => ()
    }
  }

  /** The coproducts of 𝒮: tagged unions, with the empty type 0 as initial object. */
  object Coproduct extends Cocartesian(Total, Type.TIsType[Nothing], EitherIsBifunctor) {
    def inl[A: Type, B: Type]: A -> Either[A, B] = {
      a => Left(a)
    }

    def inr[A: Type, B: Type]: B -> Either[A, B] = {
      b => Right(b)
    }

    def copair[A: Type, B: Type, X: Type](f: A -> X, g: B -> X): Either[A, B] -> X = {
      case Left(a)  => f(a)
      case Right(b) => g(b)
    }

    def absurd[A: Type]: Nothing -> A = {
      n => n
    }
  }

  /** The internal homs of 𝒮: function types, with evaluation and currying. */
  object Exponential extends Closed(Product) {
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
      * [[Limit.Cone.ConeLaws.commutes]]. So every point that exists is natural, and since clients see a point only
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

    def factor(K: Limit.Cone { val D: LimitOf.this.D.type }): K.Apex -> Point = {
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
}
