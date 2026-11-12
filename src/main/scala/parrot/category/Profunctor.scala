package parrot
package category

/** A profunctor *P*: **C₁**ᵒᵖ × **C₂** → **V**.
  *
  * Represents a profunctor *P*, where
  *   - *P*[*A*,*B*] is the object part
  *   - *P*(*f*,*g*): *P*[*A*₁,*A*₂] → *P*[*B*₁,*B*₂] is the morphism part
  *
  * A profunctor *P*: **C₁**ᵒᵖ × **C₂** → **V** is a bifunctor **C₁**ᵒᵖ × **C₂** → **V** that is contravariant in its
  * first argument and covariant in its second argument. See [[Bifunctor]].
  *
  * @see docs/TUTORIAL.md §12.4
  */
abstract class Profunctor(tracked val domain: Category, tracked val codomain: Category, tracked val base: Category)
    extends Bifunctor(domain.op, codomain, base) {
  import domain.op.--> as <--
  import codomain.--> as ->>
  import base.--> as ==>

  /** The profunctor's object part *P*. */
  final type P = Self

  /** *P* maps a pair of morphisms *f*: *B*₁ → *A*₁ of **C₁** and *g*: *A*₂ → *B*₂ of **C₂** to a morphism *P*(*f*,*g*):
    * *P*[*A*₁,*A*₂] → *P*[*B*₁,*B*₂] of **V**.
    */
  final def dimap[A1: domain.Obj, A2: codomain.Obj, B1: domain.Obj, B2: codomain.Obj](
    f: A1 <-- B1,
    g: A2 ->> B2,
  ): P[A1, A2] ==> P[B1, B2] = {
    bimap[A1, A2, B1, B2](f, g)
  }
}

object Profunctor {

  /** The profunctors into a category **V**. */
  type Into[V <: Category] = Profunctor { val base: V }
}

/** An endoprofunctor on **C** valued in **V**.
  *
  * Represents a profunctor *P*: **C**ᵒᵖ × **C** → **V**.
  */
abstract class Endoprofunctor(tracked val category: Category, tracked override val base: Category)
    extends Profunctor(category, category, base)

object Endoprofunctor {

  /** The endoprofunctors on a category **C**. */
  type On[C <: Category] = Endoprofunctor { val category: C }
}
