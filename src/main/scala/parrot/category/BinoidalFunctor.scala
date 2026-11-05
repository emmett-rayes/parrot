package parrot
package category

/** A binoidal functor *F*: **C₁** × **C₂** → **D**.
  *
  * Represents a binoidal functor, a functor in each argument separately, where
  *   - *F*[*A*₁,*A*₂] is the object part
  *   - *F*₁(*f*): *F*[*A*,*C*] → *F*[*B*,*C*] is the morphism part in the first argument
  *   - *F*₂(*g*): *F*[*C*,*A*] → *F*[*C*,*B*] is the morphism part in the second argument
  */
abstract class BinoidalFunctor(
  tracked val source1: Category,
  tracked val source2: Category,
  tracked val target: Category,
) extends caps.Pure {
  import source1.{Obj as Obj1, -->}
  import source2.{Obj as Obj2, --> as ->>}
  import target.{--> as ==>, >>>}

  type Self[_, _]

  /** The binoidal functor's object part *F*. */
  final type F = Self

  /** *F* maps a pair of objects of **C₁** and **C₂** to an object of **D**.
    */
  def objects[A: Obj1, B: Obj2]: F[A, B] is target.Obj

  /** *F* maps a morphism *f* of **C₁** to a morphism *F*₁(*f*) of **D**.
    */
  def lmap[A: Obj1, B: Obj1, C: Obj2](f: A --> B): F[A, C] ==> F[B, C]

  /** *F* maps a morphism *g* of **C₂** to a morphism *F*₂(*g*) of **D**.
    */
  def rmap[A: Obj2, B: Obj2, C: Obj1](g: A ->> B): F[C, A] ==> F[C, B]

  /** Laws that any `BinoidalFunctor` must satisfy.
    *
    * The morphism part in each argument is a functor.
    */
  object BinoidalFunctorLaws {
    private given FIsObj: [A: Obj1, B: Obj2] => (F[A, B] is target.Obj) = objects[A, B]

    /** *F*₁(*id*) = *id*
      */
    def lmapIdentity[A: Obj1, C: Obj2](using (F[A, C] ==> F[A, C]) is Observable): Boolean = {
      lmap[A, A, C](source1.identity[A]) =?= target.identity[F[A, C]]
    }

    /** *F*₁(*f*₂ ∘ *f*₁) = *F*₁(*f*₂) ∘ *F*₁(*f*₁)
      */
    def lmapComposition[A: Obj1, B: Obj1, E: Obj1, C: Obj2](f1: A --> B, f2: B --> E)(
      using (F[A, C] ==> F[E, C]) is Observable
    ): Boolean = {
      lmap[A, E, C](source1.andThen(f1, f2)) =?= (lmap[A, B, C](f1) >>> lmap[B, E, C](f2))
    }

    /** If *f* = *f*′, then *F*₁(*f*) = *F*₁(*f*′).
      *
      * @note The premise is not checked: *f*′ must be equal to *f* by construction.
      */
    def lmapCongruence[A: Obj1, B: Obj1, C: Obj2](f: A --> B, f2: A --> B)(
      using (F[A, C] ==> F[B, C]) is Observable
    ): Boolean = {
      lmap[A, B, C](f) =?= lmap[A, B, C](f2)
    }

    /** *F*₂(*id*) = *id*
      */
    def rmapIdentity[A: Obj2, C: Obj1](using (F[C, A] ==> F[C, A]) is Observable): Boolean = {
      rmap[A, A, C](source2.identity[A]) =?= target.identity[F[C, A]]
    }

    /** *F*₂(*g*₂ ∘ *g*₁) = *F*₂(*g*₂) ∘ *F*₂(*g*₁)
      */
    def rmapComposition[A: Obj2, B: Obj2, E: Obj2, C: Obj1](g1: A ->> B, g2: B ->> E)(
      using (F[C, A] ==> F[C, E]) is Observable
    ): Boolean = {
      rmap[A, E, C](source2.andThen(g1, g2)) =?= (rmap[A, B, C](g1) >>> rmap[B, E, C](g2))
    }

    /** If *g* = *g*′, then *F*₂(*g*) = *F*₂(*g*′).
      *
      * @note The premise is not checked: *g*′ must be equal to *g* by construction.
      */
    def rmapCongruence[A: Obj2, B: Obj2, C: Obj1](g: A ->> B, g2: A ->> B)(
      using (F[C, A] ==> F[C, B]) is Observable
    ): Boolean = {
      rmap[A, B, C](g) =?= rmap[A, B, C](g2)
    }
  }
}

object BinoidalFunctor {

  /** The binoidal functors into a category **D**. */
  type Into[D <: Category] = BinoidalFunctor { val target: D }
}
