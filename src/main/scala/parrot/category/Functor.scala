package parrot
package category

/** A functor *F*: **C** → **D**.
  *
  * Represents a functor, where
  *   - *F*[*A*] is the object part, a type constructor
  *   - *F*(*f*): *F*[*A*] → *F*[*B*] is the morphism part, a program
  */
abstract class Functor(tracked val C: Category, tracked val D: Category) extends caps.Pure {
  import C.-->
  import D.{--> as ->>}

  type Self[_]

  /** The object part *F*. */
  final type F = Self

  /** *F* maps objects to objects.
    */
  def objects[A: C.Obj]: F[A] is D.Obj

  /** The morphism part *F*(*f*). */
  def map[A: C.Obj, B: C.Obj](f: A --> B): F[A] ->> F[B]

  /** Laws that any `Functor` must satisfy. */
  object FunctorLaws {
    private given FIsObj: [A: C.Obj] => (F[A] is D.Obj) = objects[A]

    /** *F*(*id*) = *id*
      */
    def identity[A: C.Obj](using (F[A] ->> F[A]) is Observable): Boolean = {
      map(C.identity[A]) =?= D.identity[F[A]]
    }

    /** *F*(*g* ∘ *f*) = *F*(*g*) ∘ *F*(*f*)
      */
    def composition[A: C.Obj, B: C.Obj, E: C.Obj](f: A --> B, g: B --> E)(
      using (F[A] ->> F[E]) is Observable
    ): Boolean = {
      map(C.compose(g, f)) =?= D.compose(map(g), map(f))
    }

    /** If *f* = *f*′, then *F*(*f*) = *F*(*f*′).
      *
      * @note The premise is not checked: *f*′ must be equal to *f* by construction.
      */
    def congruence[A: C.Obj, B: C.Obj](f: A --> B, f2: A --> B)(using (F[A] ->> F[B]) is Observable): Boolean = {
      map(f) =?= map(f2)
    }
  }
}

/** An endofunctor on **K**: a functor from **K** to itself.
  *
  * Represents a functor *F*: **K** → **K**; monads ([[Monad]]) are structure on an endofunctor.
  */
abstract class Endofunctor(tracked val K: Category) extends Functor(K, K)

object Endofunctor {

  /** `Option` as an endofunctor on 𝒮, where
    *   - *F*[*A*] = *A* + 1: a value or none
    *   - *F*(*f*) applies *f* to a value and keeps none
    */
  object OptionIsEndofunctor extends Endofunctor(Total) {
    type Self = Option

    def objects[A: Type]: Option[A] is Type = {
      Type.TIsType
    }

    def map[A: Type, B: Type](f: A -> B): Option[A] -> Option[B] = {
      _.map(f)
    }
  }
}
