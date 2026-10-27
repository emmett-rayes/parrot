package parrot
package category

/** A profunctor *P*: **K**ᵒᵖ × **K** → **V**: a bifunctor that is contravariant in its first argument.
  *
  * Represents a profunctor, where
  *   - *P*[*A*,*B*] = `P[A, B]` = `Self[A, B]` is the object part
  *   - *P*(*f*,*g*): *P*[*A*,*B*] → *P*[*A*₂,*B*₂] is the morphism part, for *f*: *A*₂ → *A* and *g*: *B* → *B*₂ in
  *     **K**: precompose with *f*, postcompose with *g*
  *
  * Morphisms of **K** are written `A --> B` and of **V** `A ==> B`; implementations of `bimap` write those of **K**ᵒᵖ
  * as `A ~~> B`. A profunctor is the [[Bifunctor]] **K**ᵒᵖ × **K** → **V**; `dimap` is its morphism part with the
  * variance spelled out.
  */
abstract class Profunctor(tracked val K: Category, tracked val V: Category) extends Bifunctor(K.op, K, V) {
  import K.{Obj, -->}
  import V.{--> as ==>}

  /** The object part *P*. */
  final type P = Self

  /** *P*(*f*,*g*) for *f*: *A*₂ → *A* and *g*: *B* → *B*₂ in **K**.
    */
  final def dimap[A: Obj, B: Obj, A2: Obj, B2: Obj](f: A2 --> A, g: B --> B2): P[A, B] ==> P[A2, B2] = {
    bimap[A, B, A2, B2](f, g)
  }
}
