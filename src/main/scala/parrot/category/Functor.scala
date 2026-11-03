package parrot
package category

/** A functor *F*: **C** → **D**.
  *
  * Represents a functor, where
  *   - *F*[*A*] is the object part
  *   - *F*(*f*): *F*[*A*] → *F*[*B*] is the morphism part
  */
abstract class Functor(tracked val source: Category, tracked val target: Category) extends caps.Pure {
  import source.-->
  import target.--> as ==>

  type Self[_]

  /** The functor's object part *F*. */
  final type F = Self

  /** *F* maps an object of **C** to an object of **D**.
    */
  def objects[A: source.Obj]: F[A] is target.Obj

  /** *F* maps a morphism *f* of **C** to a morphism *F*(*f*) of **D**.
    */
  def map[A: source.Obj, B: source.Obj](f: A --> B): F[A] ==> F[B]

  /** Laws that any `Functor` must satisfy. */
  object FunctorLaws {
    private given FIsObj: [A: source.Obj] => (F[A] is target.Obj) = objects[A]

    /** *F*(*id*) = *id*
      */
    def identity[A: source.Obj](using (F[A] ==> F[A]) is Observable): Boolean = {
      map(source.identity[A]) =?= target.identity[F[A]]
    }

    /** *F*(*g* ∘ *f*) = *F*(*g*) ∘ *F*(*f*)
      */
    def composition[A: source.Obj, B: source.Obj, E: source.Obj](f: A --> B, g: B --> E)(
      using (F[A] ==> F[E]) is Observable
    ): Boolean = {
      map(f >>> g) =?= map(f) >>> map(g)
    }

    /** If *f* = *f*′, then *F*(*f*) = *F*(*f*′).
      *
      * @note The premise is not checked: *f*′ must be equal to *f* by construction.
      */
    def congruence[A: source.Obj, B: source.Obj](f: A --> B, f2: A --> B)(
      using (F[A] ==> F[B]) is Observable
    ): Boolean = {
      map(f) =?= map(f2)
    }
  }
}

object Functor {

  /** The functors into a category **D**. */
  type Into[D <: Category] = Functor { val target: D }
}

/** An endofunctor on a category **K**.
  *
  * Represents a functor *F*: **K** → **K**.
  */
abstract class Endofunctor(tracked val category: Category) extends Functor(category, category)

object Endofunctor {

  /** The endofunctors on a category **K**. */
  type On[K <: Category] = Endofunctor { val category: K }
}
