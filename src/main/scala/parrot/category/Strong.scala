package parrot
package category

/** A strong profunctor *P*: **K₁**ᵒᵖ × **K₂** → **V** over left modules (also called a Tambara module).
  *
  * Represents a strong profunctor over two **M**-modules, where
  *   - ⊘₁: **M** × **K₁** → **K₁** is the left action of **M** on **K₁**
  *   - ⊘₂: **M** × **K₂** → **K₂** is the left action of **M** on **K₂**
  *   - *τ*: *P*(*A*,*B*) → *P*(*C* ⊘₁ *A*,*C* ⊘₂ *B*) is the left strength, an arrow of **V**
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
  import monoidal.category.Obj as ObjM
  import monoidal.`*`
  import module1.`~` as `~1`
  import module2.`~` as `~2`

  private given IIsObj: (monoidal.I is ObjM) = monoidal.unit.evidence

  private given TensorIsObj: [C: ObjM, D: ObjM] => ((C * D) is ObjM) = monoidal.tensor.objects[C, D]

  private given Action1IsObj: [C: ObjM, A: Obj1] => ((C `~1` A) is Obj1) = module1.action.objects[C, A]

  private given Action2IsObj: [C: ObjM, B: Obj2] => ((C `~2` B) is Obj2) = module2.action.objects[C, B]

  private given PIsObj: [A: Obj1, B: Obj2] => (P[A, B] is ObjV) = profunctor.objects[A, B]

  /** The left strength *τ*: *P*(*A*,*B*) → *P*(*C* ⊘₁ *A*,*C* ⊘₂ *B*).
    */
  def left[A: Obj1, B: Obj2, C: ObjM]: P[A, B] ==> P[C `~1` A, C `~2` B]

  /** Laws that any `Strong` profunctor must satisfy.
    *
    * The left strength is natural in *A* and *B*, dinatural in *C*, and compatible with the unitors and associators of
    * the actions.
    */
  object StrongLaws {

    /** *τ* ∘ *P*(*f*,*g*) = *P*(*id* ⊘₁ *f*,*id* ⊘₂ *g*) ∘ *τ*
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

    /** *P*(*h* ⊘₁ *id*,*id*) ∘ *τ* = *P*(*id*,*h* ⊘₂ *id*) ∘ *τ*, dinaturality in *C*
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

object Strong {

  /** A bistrong structure on a profunctor *P*: **K**ᵒᵖ × **K** → **V**, over a symmetric monoidal category **M** acting on
    * itself.
    *
    * Represents a bistrong profunctor over the self-action of **M**, where
    *   - ⊗: **K** × **K** → **K** is the tensor of **M**, which acts on **K** from both sides
    *   - *τ*: *P*(*A*,*B*) → *P*(*C* ⊗ *A*,*C* ⊗ *B*) is the left strength
    *   - *τ*′: *P*(*A*,*B*) → *P*(*A* ⊗ *C*,*B* ⊗ *C*) is the right strength derived from the left strength
    *
    * Here, the action is ⊗ itself because a right strength needs a right action, which a left module does not have.
    */
  abstract class Bistrong(
    tracked override val profunctor: Profunctor { val codomain: domain.type },
    tracked override val monoidal: Symmetric.On[profunctor.domain.type],
  ) extends Strong(profunctor, monoidal, Module.OfMonoidal(monoidal), Module.OfMonoidal(monoidal)) {
    import monoidal.`*`
    import profunctor.P
    import profunctor.base.{Obj as ObjV, --> as ==>, >>>}
    import monoidal.category.Obj

    private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = monoidal.tensor.objects[A, B]

    private given PIsObj: [A: Obj, B: Obj] => (P[A, B] is ObjV) = profunctor.objects[A, B]

    /** The right strength *τ*′: *P*(*A*,*B*) → *P*(*A* ⊗ *C*,*B* ⊗ *C*), an arrow of **V**.
      *
      * The right strength is derived from the left strength as *P*(*β*,*β*) ∘ *τ*.
      */
    def right[A: Obj, B: Obj, C: Obj]: P[A, B] ==> P[A * C, B * C] = {
      left[A, B, C] >>> profunctor.dimap(monoidal.braid[A, C], monoidal.braid[C, B])
    }

    /** Laws that any `Bistrong` profunctor must satisfy.
      *
      * The left and the right strength commute, up to the associator.
      */
    object BistrongLaws {

      /** *τ*′ ∘ *τ* = *P*(*α*,*α*⁻¹) ∘ *τ* ∘ *τ*′
        */
      def compatibility[A: Obj, B: Obj, C: Obj, D: Obj](
        using (P[A, B] ==> P[(C * A) * D, (C * B) * D]) is Observable
      ): Boolean = {
        val associators = profunctor.dimap(monoidal.associator[C, A, D].to, monoidal.associator[C, B, D].from)
        (left[A, B, C] >>> right[C * A, C * B, D]) =?= (right[A, B, D] >>> left[A * D, B * D, C] >>> associators)
      }
    }
  }

  object Bistrong {

    /** The bistrong structures on a profunctor *P*. */
    type On[P <: Profunctor] = Bistrong { val profunctor: P }

    /** The opposite *P*ᵒᵖ of a bistrong promonad *P*, over **M**ᵒᵖ.
      *
      * The opposite has the same left strength, with every morphism reversed.
      *
      * @note **M** is meant to be `strong.monoidal.op`; its braiding is not checked.
      */
    final class Op(
      tracked val strong: Bistrong.On[Promonad],
      tracked override val monoidal: Symmetric.On[strong.profunctor.category.op.type] {
        val tensor: Bifunctor { type Self = strong.monoidal.tensor.F }
      },
    ) extends Bistrong(Promonad.Op(strong.profunctor), monoidal) {
      import monoidal.`*`
      import profunctor.P
      import profunctor.category.Obj

      def left[A: Obj, B: Obj, C: Obj]: P[A, B] -> P[C * A, C * B] = {
        strong.left[B, A, C]
      }
    }

    /** The bistrong hom promonad of a symmetric monoidal category **M**: *τ*(*f*) = *id* ⊗ *f*.
      *
      * Every symmetric monoidal category is bistrong over itself in this way.
      */
    open class Hom(
      tracked override val profunctor: Promonad.Hom,
      tracked override val monoidal: Symmetric.On[profunctor.category.type],
    ) extends Bistrong(profunctor, monoidal) {
      import monoidal.`*`
      import profunctor.category.{Obj, -->}

      def left[A: Obj, B: Obj, C: Obj]: (A --> B) -> ((C * A) --> (C * B)) = {
        p => monoidal.parallel(profunctor.category.identity[C], p)
      }
    }
  }
}
