package parrot
package category

/** A functor *F*: **C** → **D**.
  *
  * Represents a functor *F*, where
  *   - *F*[*A*] is the object part
  *   - *F*(*f*): *F*[*A*] → *F*[*B*] is the morphism part
  *
  * @see docs/TUTORIAL.md §12.2
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

  /** The composite *G* ∘ *F*: **C** → **E** of *F*: **C** → **D** and *G*: **D** → **E**, where
    *   - (*G* ∘ *F*)[*A*] = *G*[*F*[*A*]]
    *   - (*G* ∘ *F*)(*f*) = *G*(*F*(*f*))
    */
  open class Composite(tracked val first: Functor, tracked val second: Functor { val source: first.target.type })
      extends Functor(first.source, second.target) {
    type Self[A] = second.F[first.F[A]]

    def objects[A: first.source.Obj]: second.F[first.F[A]] is second.target.Obj = {
      second.objects[first.F[A]](using first.objects[A])
    }

    def map[A: first.source.Obj, B: first.source.Obj](
      f: first.source.Hom[A, B]
    ): second.target.Hom[second.F[first.F[A]], second.F[first.F[B]]] = {
      second.map[first.F[A], first.F[B]](first.map(f))(using first.objects[A], first.objects[B])
    }
  }
}

/** An endofunctor on a category **C**.
  *
  * Represents a functor *F*: **C** → **C**.
  */
abstract class Endofunctor(tracked val category: Category) extends Functor(category, category)

object Endofunctor {

  /** The endofunctors on a category **C**. */
  type On[C <: Category] = Endofunctor { val category: C }

  /** The identity functor *Id* on a category **C**, where
    *   - *Id*[*A*] = *A*
    *   - *Id*(*f*) = *f*
    */
  open class Identity(tracked override val category: Category) extends Endofunctor(category) {
    type Self[A] = A

    def objects[A: category.Obj as obj]: A is category.Obj = {
      obj
    }

    def map[A: category.Obj, B: category.Obj](f: category.Hom[A, B]): category.Hom[A, B] = {
      f
    }
  }
}
