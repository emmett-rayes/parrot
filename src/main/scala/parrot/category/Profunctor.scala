package parrot
package category

/** A profunctor *P*: **K₁**ᵒᵖ × **K₂** → **V**.
  *
  * Represents a profunctor, where
  *   - *P*[*A*,*B*] is the object part
  *   - *P*(*f*,*g*): *P*[*A*₁,*A*₂] → *P*[*B*₁,*B*₂] is the morphism part, for *f*: *B*₁ → *A*₁ in **K₁** and *g*: *A*₂
  *     → *B*₂ in **K₂**: precompose with *f*, postcompose with *g*
  *
  * A profunctor *P*: **K₁**ᵒᵖ × **K₂** → **V** is a bifunctor **K₁**ᵒᵖ × **K₂** → **V** that is contravariant in its
  * first argument and covariant in its second argument. See [[Bifunctor]].
  */
abstract class Profunctor(tracked val domain: Category, tracked val codomain: Category, tracked val base: Category)
    extends Bifunctor(domain.op, codomain, base) {
  import domain.-->
  import codomain.--> as ->>
  import base.--> as ==>

  /** The object part *P*. */
  final type P = Self

  /** *P* maps a pair of morphisms *f*: *B*₁ → *A*₁ of **K₁** and *g*: *A*₂ → *B*₂ of **K₂** to a morphism *P*(*f*,*g*):
    * *P*[*A*₁,*A*₂] → *P*[*B*₁,*B*₂] of **V**.
    */
  final def dimap[A1: domain.Obj, A2: codomain.Obj, B1: domain.Obj, B2: codomain.Obj](
    f: B1 --> A1,
    g: A2 ->> B2,
  ): P[A1, A2] ==> P[B1, B2] = {
    bimap[A1, A2, B1, B2](f, g)
  }
}

/** An endoprofunctor on **K** valued in **V**.
  *
  * Represents a profunctor *P*: **K**ᵒᵖ × **K** → **V**.
  */
abstract class Endoprofunctor(tracked val category: Category, tracked override val base: Category)
    extends Profunctor(category, category, base)
