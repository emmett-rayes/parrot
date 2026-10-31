package parrot
package category

/** A profunctor *P*: **K₁**ᵒᵖ × **K₂** → **V**.
  *
  * Represents a profunctor, where
  *   - *P*[*A*,*B*] is the object part
  *   - *P*(*f*,*g*): *P*[*A*₁,*B*₁] → *P*[*A*₂,*B*₂] is the morphism part, for *f*: *A*₂ → *A*₁ in **K₁** and *g*: *B*₁
  *     → *B*₂ in **K₂**: precompose with *f*, postcompose with *g*
  *
  * A profunctor *P*: **K₁**ᵒᵖ × **K₂** → **V** is a bifunctor **K₁**ᵒᵖ × **K₂** → **V** that is contravariant in its
  * first argument and covariant in its second argument. See [[Bifunctor]].
  */
abstract class Profunctor(tracked val K1: Category, tracked val K2: Category, tracked val V: Category)
    extends Bifunctor(K1.op, K2, V) {
  import K1.-->
  import K2.--> as ->>
  import V.--> as ==>

  /** The object part *P*. */
  final type P = Self

  /** *P* maps a pair of morphisms *f*: *A*₂ → *A*₁ of **K₁** and *g*: *B*₁ → *B*₂ of **K₂** to a morphism *P*(*f*,*g*):
    * *P*[*A*₁,*B*₁] → *P*[*A*₂,*B*₂] of **V**.
    */
  final def dimap[A1: K1.Obj, B1: K2.Obj, A2: K1.Obj, B2: K2.Obj](
    f: A2 --> A1,
    g: B1 ->> B2,
  ): P[A1, B1] ==> P[A2, B2] = {
    bimap[A1, B1, A2, B2](f, g)
  }
}

/** An endoprofunctor on **K** valued in **V**.
  *
  * Represents a profunctor *P*: **K**ᵒᵖ × **K** → **V**.
  */
abstract class Endoprofunctor(tracked val K: Category, tracked override val V: Category) extends Profunctor(K, K, V)
