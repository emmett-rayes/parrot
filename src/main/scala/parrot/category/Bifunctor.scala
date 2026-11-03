package parrot
package category

/** A bifunctor *F*: **C₁** × **C₂** → **D**.
  *
  * Represents a bifunctor, where
  *   - *F*[*A*,*B*] is the object part
  *   - *F*(*f*,*g*): *F*[*A*₁,*A*₂] → *F*[*B*₁,*B*₂] is the morphism part
  */
abstract class Bifunctor(tracked val source1: Category, tracked val source2: Category, tracked val target: Category)
    extends caps.Pure {
  import source1.{Obj as Obj1, -->}
  import source2.{Obj as Obj2, --> as ->>}
  import target.--> as ==>

  type Self[_, _]

  /** The bifunctor's object part *F*. */
  final type F = Self

  /** *F* maps a pair of objects of **C₁** and **C₂** to an object of **D**.
    */
  def objects[A: Obj1, B: Obj2]: F[A, B] is target.Obj

  /** *F* maps a pair of morphisms *f* of **C₁** and *g* of **C₂** to a morphism *F*(*f*,*g*) of **D**.
    */
  def bimap[A1: Obj1, A2: Obj2, B1: Obj1, B2: Obj2](f: A1 --> B1, g: A2 ->> B2): F[A1, A2] ==> F[B1, B2]

  /** The bifunctor as a functor out of the product category **C₁** × **C₂**. */
  final lazy val functor: Bifunctor.FromProduct { val bifunctor: Bifunctor.this.type } = Bifunctor.FromProduct(this)

  /** The corresponding opposite bifunctor *F*ᵒᵖ: **C₁**ᵒᵖ × **C₂**ᵒᵖ → **D**ᵒᵖ. */
  final lazy val op: Bifunctor.Op { val bifunctor: Bifunctor.this.type } = Bifunctor.Op(this)

  /** Laws that any `Bifunctor` must satisfy. */
  object BifunctorLaws {
    import functor.source.given
    import functor.FunctorLaws

    /** *F*(*id*,*id*) = *id*
      */
    def identity[A: Obj1, B: Obj2](using (F[A, B] ==> F[A, B]) is Observable): Boolean = {
      FunctorLaws.identity[(A, B)]
    }

    /** *F*(*f*₂ ∘ *f*₁,*g*₂ ∘ *g*₁) = *F*(*f*₂,*g*₂) ∘ *F*(*f*₁,*g*₁)
      */
    def composition[A1: Obj1, A2: Obj2, B1: Obj1, B2: Obj2, E1: Obj1, E2: Obj2](
      f1: A1 --> B1,
      g1: A2 ->> B2,
      f2: B1 --> E1,
      g2: B2 ->> E2,
    )(using (F[A1, A2] ==> F[E1, E2]) is Observable): Boolean = {
      FunctorLaws.composition[(A1, A2), (B1, B2), (E1, E2)]((f1, g1), (f2, g2))
    }

    /** If *f* = *f*′ and *g* = *g*′, then *F*(*f*,*g*) = *F*(*f*′,*g*′).
      *
      * @note The premise is not checked: *f*′ and *g*′ must be equal to *f* and *g* by construction.
      */
    def congruence[A1: Obj1, A2: Obj2, B1: Obj1, B2: Obj2](
      f: A1 --> B1,
      f2: A1 --> B1,
      g: A2 ->> B2,
      g2: A2 ->> B2,
    )(using (F[A1, A2] ==> F[B1, B2]) is Observable): Boolean = {
      FunctorLaws.congruence[(A1, A2), (B1, B2)]((f, g), (f2, g2))
    }
  }
}

object Bifunctor {

  /** A bifunctor *F*: **C₁** × **C₂** → **D**, read as a functor from the product category **C₁** × **C₂** to **D**.
    *
    * Represents a functor, where
    *   - *F*(*X*) = *F*(*X*₁,*X*₂) for a pair type *X*
    *   - *F*(*f*) = *F*(*f*₁,*f*₂) for a pair of morphisms *f*
    */
  final class FromProduct(tracked val bifunctor: Bifunctor)
      extends Functor(Category.Product(bifunctor.source1, bifunctor.source2), bifunctor.target) {
    import source.-->
    import target.--> as ==>
    import Category.Product.{Fst, Snd}

    type Self[X] = bifunctor.F[Fst[X], Snd[X]]

    def objects[X: source.Obj]: F[X] is target.Obj = {
      bifunctor.objects[Fst[X], Snd[X]](using X.fst, X.snd)
    }

    def map[X: source.Obj, Y: source.Obj](f: X --> Y): F[X] ==> F[Y] = {
      bifunctor.bimap(f._1, f._2)(using X.fst, X.snd, Y.fst, Y.snd)
    }
  }

  /** The opposite *F*ᵒᵖ: **C₁**ᵒᵖ × **C₂**ᵒᵖ → **D**ᵒᵖ of a bifunctor *F*: **C₁** × **C₂** → **D**.
    *
    * The opposite bifunctor has the same object part, with every morphism reversed.
    */
  final class Op(tracked val bifunctor: Bifunctor)
      extends Bifunctor(bifunctor.source1.op, bifunctor.source2.op, bifunctor.target.op) {
    import bifunctor.source1.-->
    import bifunctor.source2.--> as ->>
    import bifunctor.target.--> as ==>

    type Self = bifunctor.F

    def objects[X: source1.Obj, Y: source2.Obj]: F[X, Y] is target.Obj = {
      bifunctor.objects[X, Y]
    }

    def bimap[A1: source1.Obj, A2: source2.Obj, B1: source1.Obj, B2: source2.Obj](
      f: B1 --> A1,
      g: B2 ->> A2,
    ): F[B1, B2] ==> F[A1, A2] = {
      bifunctor.bimap(f, g)
    }
  }
}

/** An endobifunctor on a category **K**.
  *
  * Represents a bifunctor *F*: **K** × **K** → **K**.
  */
abstract class Endobifunctor(tracked val category: Category) extends Bifunctor(category, category, category)

object Endobifunctor {

  /** The endobifunctors on a category **K**. */
  type On[K <: Category] = Endobifunctor { val category: K }
}
