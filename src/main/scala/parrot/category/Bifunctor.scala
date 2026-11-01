package parrot
package category

/** A bifunctor *F*: **C₁** × **C₂** → **D**.
  *
  * Represents a bifunctor, where
  *   - *F*[*A*,*B*] is the object part
  *   - *F*(*f*,*g*): *F*[*A*₁,*A*₂] → *F*[*B*₁,*B*₂] is the morphism part
  */
abstract class Bifunctor(tracked val C1: Category, tracked val C2: Category, tracked val D: Category)
    extends caps.Pure {
  import C1.-->
  import C2.--> as ->>
  import D.--> as ==>

  type Self[_, _]

  /** The bifunctor's object part *F*. */
  final type F = Self

  /** *F* maps a pair of objects of **C₁** and **C₂** to an object of **D**.
    */
  def objects[A: C1.Obj, B: C2.Obj]: F[A, B] is D.Obj

  /** Evidence that *F*[*A*,*B*] is an object of **D** for objects *A* and *B*, for clients of the structure. */
  given FIsObj: [A: C1.Obj, B: C2.Obj] => (F[A, B] is D.Obj) = objects[A, B]

  /** *F* maps a pair of morphisms *f* of **C₁** and *g* of **C₂** to a morphism *F*(*f*,*g*) of **D**.
    */
  def bimap[A1: C1.Obj, A2: C2.Obj, B1: C1.Obj, B2: C2.Obj](f: A1 --> B1, g: A2 ->> B2): F[A1, A2] ==> F[B1, B2]

  /** The bifunctor as a functor out of the product category **C₁** × **C₂**: *F*(*X*) = *F*(*X*₁,*X*₂). */
  final lazy val functor: Bifunctor.FromProduct { val B: Bifunctor.this.type } = Bifunctor.FromProduct(this)

  /** The corresponding opposite bifunctor *F*ᵒᵖ: **C₁**ᵒᵖ × **C₂**ᵒᵖ → **D**ᵒᵖ. */
  final lazy val op: Bifunctor.Op { val B: Bifunctor.this.type } = Bifunctor.Op(this)

  /** Laws that any `Bifunctor` must satisfy. */
  object BifunctorLaws {
    import functor.C.given

    /** *F*(*id*,*id*) = *id*
      */
    def identity[A: C1.Obj, B: C2.Obj](using (F[A, B] ==> F[A, B]) is Observable): Boolean = {
      functor.FunctorLaws.identity[(A, B)]
    }

    /** *F*(*f*₂ ∘ *f*₁,*g*₂ ∘ *g*₁) = *F*(*f*₂,*g*₂) ∘ *F*(*f*₁,*g*₁)
      */
    def composition[A1: C1.Obj, A2: C2.Obj, B1: C1.Obj, B2: C2.Obj, E1: C1.Obj, E2: C2.Obj](
      f1: A1 --> B1,
      g1: A2 ->> B2,
      f2: B1 --> E1,
      g2: B2 ->> E2,
    )(using (F[A1, A2] ==> F[E1, E2]) is Observable): Boolean = {
      functor.FunctorLaws.composition[(A1, A2), (B1, B2), (E1, E2)]((f1, g1), (f2, g2))
    }

    /** If *f* = *f*′ and *g* = *g*′, then *F*(*f*,*g*) = *F*(*f*′,*g*′).
      *
      * @note The premise is not checked: *f*′ and *g*′ must be equal to *f* and *g* by construction.
      */
    def congruence[A1: C1.Obj, A2: C2.Obj, B1: C1.Obj, B2: C2.Obj](
      f: A1 --> B1,
      f2: A1 --> B1,
      g: A2 ->> B2,
      g2: A2 ->> B2,
    )(using (F[A1, A2] ==> F[B1, B2]) is Observable): Boolean = {
      functor.FunctorLaws.congruence[(A1, A2), (B1, B2)]((f, g), (f2, g2))
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
    import D.--> as ==>
    import Category.Product.{Fst, Snd}

    type Self[X] = B.F[Fst[X], Snd[X]]

    def objects[X: C.Obj]: F[X] is D.Obj = {
      B.objects[Fst[X], Snd[X]](using X.fst, X.snd)
    }

    def map[X: C.Obj, Y: C.Obj](f: X --> Y): F[X] ==> F[Y] = {
      B.bimap(f._1, f._2)(using X.fst, X.snd, Y.fst, Y.snd)
    }
  }

  /** The opposite *F*ᵒᵖ: **C₁**ᵒᵖ × **C₂**ᵒᵖ → **D**ᵒᵖ of a bifunctor *F*: **C₁** × **C₂** → **D**.
    *
    * The opposite bifunctor has the same object part, with every morphism reversed.
    */
  final class Op(tracked val B: Bifunctor) extends Bifunctor(B.C1.op, B.C2.op, B.D.op) {
    import B.C1.-->
    import B.C2.--> as ->>
    import B.D.--> as ==>

    type Self = B.F

    def objects[X: C1.Obj, Y: C2.Obj]: F[X, Y] is D.Obj = {
      B.objects[X, Y]
    }

    def bimap[A1: C1.Obj, A2: C2.Obj, B1: C1.Obj, B2: C2.Obj](f: B1 --> A1, g: B2 ->> A2): F[B1, B2] ==> F[A1, A2] = {
      B.bimap(f, g)
    }
  }
}

/** An endobifunctor on **K**.
  *
  * Represents a bifunctor *F*: **K** × **K** → **K**.
  */
abstract class Endobifunctor(tracked val K: Category) extends Bifunctor(K, K, K)

object Endobifunctor {

  /** The endobifunctors on **K**. */
  type On[K <: Category] = Endobifunctor { val K: K }

  /** The opposite *F*ᵒᵖ: **K**ᵒᵖ × **K**ᵒᵖ → **K**ᵒᵖ of an endobifunctor *F* on **K**.
    *
    * The opposite endobifunctor has the same object part, with every morphism reversed.
    *
    * @note [[Bifunctor.op]] is the same bifunctor, but as a bifunctor between three categories: it is not known to be
    *   an endobifunctor.
    */
  final class Op(tracked val B: Endobifunctor) extends Endobifunctor(B.K.op) {
    import B.K.-->

    type Self = B.F

    def objects[X: K.Obj, Y: K.Obj]: F[X, Y] is K.Obj = {
      B.objects[X, Y]
    }

    def bimap[A1: K.Obj, A2: K.Obj, B1: K.Obj, B2: K.Obj](f: B1 --> A1, g: B2 --> A2): F[B1, B2] --> F[A1, A2] = {
      B.bimap(f, g)
    }
  }
}
