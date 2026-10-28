package parrot
package category

/** A bifunctor *F*: **C₁** × **C₂** → **D**: a functor of two arguments, one from each source category.
  *
  * Represents a bifunctor, where
  *   - *F*[*A*,*B*] is the object part
  *   - *F*(*f*,*g*): *F*[*A*,*B*] → *F*[*A*₂,*B*₂] is the morphism part, for *f*: *A* → *A*₂ in **C₁** and *g*: *B* →
  *     *B*₂ in **C₂**
  */
abstract class Bifunctor(tracked val C1: Category, tracked val C2: Category, tracked val D: Category)
    extends caps.Pure {
  import C1.-->
  import C2.{--> as ->>}
  import D.{--> as ==>}

  type Self[_, _]

  /** The object part *F*. */
  final type F = Self

  /** *F* maps pairs of objects to objects.
    */
  def objects[A: C1.Obj, B: C2.Obj]: F[A, B] is D.Obj

  /** The morphism part *F*(*f*,*g*). */
  def bimap[A: C1.Obj, B: C2.Obj, A2: C1.Obj, B2: C2.Obj](f: A --> A2, g: B ->> B2): F[A, B] ==> F[A2, B2]

  /** The bifunctor as a functor out of the product category **C₁** × **C₂**: *F*(*X*) = *F*(*X*₁,*X*₂). */
  final lazy val functor: Bifunctor.FromProduct { val B: Bifunctor.this.type } = Bifunctor.FromProduct(this)

  /** Laws that any `Bifunctor` must satisfy: the [[Functor.FunctorLaws]] of [[functor]], at pairs of objects. */
  object BifunctorLaws {
    import functor.C.given

    /** *F*(*id*,*id*) = *id*
      */
    def identity[A: C1.Obj, B: C2.Obj](using (F[A, B] ==> F[A, B]) is Observable): Boolean = {
      functor.FunctorLaws.identity[(A, B)]
    }

    /** *F*(*f*₂ ∘ *f*₁,*g*₂ ∘ *g*₁) = *F*(*f*₂,*g*₂) ∘ *F*(*f*₁,*g*₁)
      */
    def composition[A: C1.Obj, B: C2.Obj, A2: C1.Obj, B2: C2.Obj, A3: C1.Obj, B3: C2.Obj](
      f1: A --> A2,
      g1: B ->> B2,
      f2: A2 --> A3,
      g2: B2 ->> B3,
    )(using (F[A, B] ==> F[A3, B3]) is Observable): Boolean = {
      functor.FunctorLaws.composition[(A, B), (A2, B2), (A3, B3)]((f1, g1), (f2, g2))
    }

    /** If *f* = *f*′ and *g* = *g*′, then *F*(*f*,*g*) = *F*(*f*′,*g*′).
      *
      * @note The premise is not checked: *f*′ and *g*′ must be equal to *f* and *g* by construction.
      */
    def congruence[A: C1.Obj, B: C2.Obj, A2: C1.Obj, B2: C2.Obj](
      f: A --> A2,
      f2: A --> A2,
      g: B ->> B2,
      g2: B ->> B2,
    )(using (F[A, B] ==> F[A2, B2]) is Observable): Boolean = {
      functor.FunctorLaws.congruence[(A, B), (A2, B2)]((f, g), (f2, g2))
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
  final class FromProduct(tracked val B: Bifunctor) extends Functor(Category.Product(B.C1, B.C2), B.D) {
    import C.-->
    import D.{--> as ->>}
    import Category.Product.{Fst, Snd}

    type Self[X] = B.F[Fst[X], Snd[X]]

    def objects[X: C.Obj]: F[X] is D.Obj = {
      B.objects[Fst[X], Snd[X]](using X.fst, X.snd)
    }

    def map[X: C.Obj, Y: C.Obj](f: X --> Y): F[X] ->> F[Y] = {
      B.bimap(f._1, f._2)(using X.fst, X.snd, Y.fst, Y.snd)
    }
  }
}
