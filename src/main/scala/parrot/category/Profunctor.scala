package parrot
package category

/** A profunctor *P*: **K**ᵒᵖ × **K** → **V**: a bifunctor that is contravariant in its first argument.
  *
  * Represents a profunctor, where
  *   - *P*[*A*,*B*] is the object part
  *   - *P*(*f*,*g*): *P*[*A*₁,*B*₁] → *P*[*A*₂,*B*₂] is the morphism part, for *f*: *A*₂ → *A*₁ and *g*: *B*₁ → *B*₂ in
  *     **K**: precompose with *f*, postcompose with *g*
  *
  * A profunctor is the [[Bifunctor]] **K**ᵒᵖ × **K** → **V**; [[dimap]] is its morphism part with the variance spelled
  * out.
  */
abstract class Profunctor(tracked val K: Category, tracked val V: Category) extends Bifunctor(K.op, K, V) {
  import K.{Obj, -->}
  import V.--> as ==>

  /** The object part *P*. */
  final type P = Self

  /** *P*(*f*,*g*) for *f*: *A*₂ → *A*₁ and *g*: *B*₁ → *B*₂ in **K**.
    */
  final def dimap[A1: Obj, B1: Obj, A2: Obj, B2: Obj](f: A2 --> A1, g: B1 --> B2): P[A1, B1] ==> P[A2, B2] = {
    bimap[A1, B1, A2, B2](f, g)
  }
}
