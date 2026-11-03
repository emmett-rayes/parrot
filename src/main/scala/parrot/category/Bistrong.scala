package parrot
package category

/** A bistrong structure on a profunctor *P*: **C**ᵒᵖ × **C** → **V**, over a symmetric monoidal category **M** acting
  * on itself.
  *
  * Represents a bistrong profunctor over the self-action of **M**, where
  *   - ⊗: **C** × **C** → **C** is the tensor of **M**, which acts on **C** from both sides
  *   - *τ*: *P*(*A*,*B*) → *P*(*C* ⊗ *A*,*C* ⊗ *B*) is the left strength
  *   - *τ*′: *P*(*A*,*B*) → *P*(*A* ⊗ *C*,*B* ⊗ *C*) is the right strength
  *
  * @note The action is ⊗ itself because a right strength needs a right action, which a left module does not have.
  */
abstract class Bistrong(
  tracked override val profunctor: Profunctor { val codomain: domain.type },
  tracked override val monoidal: Symmetric.On[profunctor.domain.type],
) extends Strong(profunctor, monoidal, Module.OfMonoidal(monoidal), Module.OfMonoidal(monoidal)) {
  import profunctor.P
  import profunctor.base.{Obj as ObjV, --> as ==>, >>>}
  import monoidal.`*`
  import monoidal.category.Obj

  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = monoidal.tensor.objects[A, B]
  private given PIsObj: [A: Obj, B: Obj] => (P[A, B] is ObjV)     = profunctor.objects[A, B]

  /** The right strength *τ*′: *P*(*A*,*B*) → *P*(*A* ⊗ *C*,*B* ⊗ *C*). */
  def right[A: Obj, B: Obj, C: Obj]: P[A, B] ==> P[A * C, B * C] = {
    left[A, B, C] >>> profunctor.dimap(monoidal.braid[A, C], monoidal.braid[C, B])
  }

  /** Laws that any `Bistrong` profunctor must satisfy. */
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

  /** The opposite *P*ᵒᵖ: **C** × **C**ᵒᵖ → 𝒮 over **M**ᵒᵖ of a bistrong promonad *P*: **C**ᵒᵖ × **C** → 𝒮 over a
    * symmetric **M**.
    *
    * The opposite bistrong promonad has the same left strength, with every morphism reversed.
    *
    * @note **M**ᵒᵖ is meant to be `strong.monoidal.op`; its braiding is not checked.
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
