package parrot
package category

import scala.annotation.targetName

/** A valued profunctor on a base category **B** over a target category **V**.
  *
  * Represents an bifunctor *P*: **B**^op × **B** → **V**, where
  *   - *P*[*A*,*B*] is the object part, contravariant in *A* and covariant in *B*
  *   - *P*(*f*,*g*) is the morphism part
  */
trait Profunctor {
  type Self[_, _]
  final type P = Self

  /** The base category **B**. */
  type B[_, _]: Category as ProfunctorOnCategory

  /** The target category **V**. */
  type V[_, _]: Category as ProfunctorOverCategory

  val BIsCategory: B is Category = ProfunctorOnCategory
  val VIsCategory: V is Category = ProfunctorOverCategory

  final type --> = B
  final type ->> = V

  /** Maps a pair of morphisms *f*: *C* --> *A* and *g*: *B* --> *D* in **B** to a morphism *P*[*A*,*B*] ->>
    * *P*[*C*,*D*] in **V**.
    */
  def dimap[A, B, C, D](f: C --> A, g: B --> D): (P[A, B]) ->> (P[C, D])

  /** Maps a morphism *f*: *C* --> *A* in **B** to a morphism *P*[*A*,*B*] ->> *P*[*C*,*B*] in **V**.
    */
  def lmap[A, B, C](f: C --> A): (P[A, B]) ->> (P[C, B]) = {
    dimap(f, B.identity[B])
  }

  /** Maps a morphism *g*: *B* --> *D* in **B** to a morphism *P*[*A*,*B*] ->> *P*[*A*,*D*] in **V**.
    */
  def rmap[A, B, D](g: B --> D): (P[A, B]) ->> (P[A, D]) = {
    dimap(B.identity[A], g)
  }

  /** Laws that any `Profunctor` must satisfy. */
  object ProfunctorLaws {

    /** *P*(*id*,*id*) = *id*
      */
    def identity[A, B](using ((P[A, B]) ->> (P[A, B])) is Eq): Boolean = {
      dimap(B.identity[A], B.identity[B]) === V.identity[P[A, B]]
    }

    /** *P*(*f*₁ ∘ *f*₂,*g*₂ ∘ *g*₁) = *P*(*f*₂,*g*₂) ∘ *P*(*f*₁,*g*₁)
      */
    def composition[A, B, C, D, E, F](
      f1: C --> A,
      g1: B --> D,
      f2: E --> C,
      g2: D --> F,
    )(using ((P[A, B]) ->> (P[E, F])) is Eq): Boolean = {
      dimap(f2 >>> f1, g1 >>> g2) === dimap(f1, g1) >>> dimap(f2, g2)
    }
  }
}

object Profunctor {

  /** Refines the base category `B` of `Profunctor` to `T`. */
  infix type on[P <: Profunctor, T[_, _]] = P { type B = T }

  /** Refines the target category `V` of `Profunctor` to `T`. */
  infix type over[P <: Profunctor, T[_, _]] = P { type V = T }

  /** Summons the `Profunctor` instance of `P`. */
  def apply[P[_, _]: Profunctor]: P is Profunctor = summon

  /** `Profunctor` instance for `=:=` on the discrete category *Ob*(**Type**) over **Type**. */
  given TypeEqIsProfunctor: =:= is Profunctor {
    type B = =:=
    type V = Function

    override given ProfunctorOnCategory: Category.TypeEqIsCategory.type = Category.TypeEqIsCategory
    override val BIsCategory: Category.TypeEqIsCategory.type            = Category.TypeEqIsCategory

    override given ProfunctorOverCategory: Category.FunctionIsCategory.type = Category.FunctionIsCategory
    override val VIsCategory: Category.FunctionIsCategory.type              = Category.FunctionIsCategory

    def dimap[A, B, C, D](f: C =:= A, g: B =:= D): (A =:= B) => (C =:= D) = {
      p => g.substituteCo(p.substituteCo(f))
    }
  }

  /** `Profunctor` instance for `Function` on the category **Type** over **Type**. */
  given FunctionIsProfunctor: Function is Profunctor {
    type B = Function
    type V = Function

    override given ProfunctorOnCategory: Category.FunctionIsCategory.type = Category.FunctionIsCategory
    override val BIsCategory: Category.FunctionIsCategory.type            = Category.FunctionIsCategory

    override given ProfunctorOverCategory: Category.FunctionIsCategory.type = Category.FunctionIsCategory
    override val VIsCategory: Category.FunctionIsCategory.type              = Category.FunctionIsCategory

    def dimap[A, B, C, D](f: C => A, g: B => D): (A => B) => (C => D) = {
      p => f.andThen(p.andThen(g))
    }
  }
}
