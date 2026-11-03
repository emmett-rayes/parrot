package parrot
package category

/** A strong profunctor *P*: **C₁**ᵒᵖ × **C₂** → **V** over two left modules (also called a Tambara module).
  *
  * Represents a strong profunctor over two left **M**-modules, where
  *   - ⊘₁: **M** × **C₁** → **C₁** is the left action of **M** on **C₁**
  *   - ⊘₂: **M** × **C₂** → **C₂** is the left action of **M** on **C₂**
  *   - *τ*: *P*(*A*,*B*) → *P*(*C* ⊘₁ *A*,*C* ⊘₂ *B*) is the left strength
  */
abstract class Strong(
  tracked val profunctor: Profunctor,
  tracked val monoidal: Monoidal,
  tracked val module1: Module.Over[monoidal.type] { val category: profunctor.domain.type },
  tracked val module2: Module.Over[monoidal.type] { val category: profunctor.codomain.type },
) extends caps.Pure {
  import profunctor.P
  import profunctor.domain.{Obj as Obj1, -->}
  import profunctor.codomain.{Obj as Obj2, --> as ->>}
  import profunctor.base.{Obj as ObjV, --> as ==>, >>>}
  import monoidal.`*`
  import monoidal.category.Obj as ObjM
  import module1.`~` as `~1`
  import module2.`~` as `~2`

  private given IIsObj: (monoidal.I is ObjM)                             = monoidal.unit.evidence
  private given PIsObj: [A: Obj1, B: Obj2] => (P[A, B] is ObjV)          = profunctor.objects[A, B]
  private given TensorIsObj: [C: ObjM, D: ObjM] => ((C * D) is ObjM)     = monoidal.tensor.objects[C, D]
  private given Action1IsObj: [C: ObjM, A: Obj1] => ((C `~1` A) is Obj1) = module1.action.objects[C, A]
  private given Action2IsObj: [C: ObjM, B: Obj2] => ((C `~2` B) is Obj2) = module2.action.objects[C, B]

  /** The left strength *τ*: *P*(*A*,*B*) → *P*(*C* ⊘₁ *A*,*C* ⊘₂ *B*). */
  def left[A: Obj1, B: Obj2, C: ObjM]: P[A, B] ==> P[C `~1` A, C `~2` B]

  /** Laws that any `Strong` profunctor must satisfy. */
  object StrongLaws {

    /** *τ* ∘ *P*(*f*,*g*) = *P*(*id* ⊘₁ *f*,*id* ⊘₂ *g*) ∘ *τ*
      *
      * *τ* is natural in *A* and *B*.
      */
    def naturality[A1: Obj1, A2: Obj2, B1: Obj1, B2: Obj2, C: ObjM](f: B1 --> A1, g: A2 ->> B2)(
      using (P[A1, A2] ==> P[C `~1` B1, C `~2` B2]) is Observable
    ): Boolean = {
      val actions = profunctor.dimap(
        module1.act(monoidal.category.identity[C], f),
        module2.act(monoidal.category.identity[C], g),
      )
      (profunctor.dimap(f, g) >>> left[B1, B2, C]) =?= (left[A1, A2, C] >>> actions)
    }

    /** *P*(*h* ⊘₁ *id*,*id*) ∘ *τ* = *P*(*id*,*h* ⊘₂ *id*) ∘ *τ*
      *
      * *τ* is dinatural in *C*.
      */
    def dinaturality[A: Obj1, B: Obj2, C1: ObjM, C2: ObjM](h: monoidal.category.Hom[C1, C2])(
      using (P[A, B] ==> P[C1 `~1` A, C2 `~2` B]) is Observable
    ): Boolean = {
      val lhs = profunctor.dimap(module1.act(h, profunctor.domain.identity[A]), profunctor.codomain.identity[C2 `~2` B])
      val rhs = profunctor.dimap(profunctor.domain.identity[C1 `~1` A], module2.act(h, profunctor.codomain.identity[B]))
      (left[A, B, C2] >>> lhs) =?= (left[A, B, C1] >>> rhs)
    }

    /** *P*(*λ*₁⁻¹,*λ*₂) ∘ *τ* = *id*
      */
    def unitality[A: Obj1, B: Obj2](using (P[A, B] ==> P[A, B]) is Observable): Boolean = {
      val unitors = profunctor.dimap(module1.leftUnitor[A].from, module2.leftUnitor[B].to)
      (left[A, B, monoidal.I] >>> unitors) =?= profunctor.base.identity[P[A, B]]
    }

    /** *P*(*α*₁,*α*₂⁻¹) ∘ *τ* ∘ *τ* = *τ*
      */
    def associativity[A: Obj1, B: Obj2, C: ObjM, D: ObjM](
      using (P[A, B] ==> P[(C * D) `~1` A, (C * D) `~2` B]) is Observable
    ): Boolean = {
      val associators = profunctor.dimap(module1.associator[C, D, A].to, module2.associator[C, D, B].from)
      (left[A, B, D] >>> left[D `~1` A, D `~2` B, C] >>> associators) =?= left[A, B, C * D]
    }
  }
}
