package parrot
package category

import scala.annotation.targetName

/** A strong profunctor *P*: **K₁**ᵒᵖ × **K₂** → 𝒮 over left modules (also called a Tambara module).
  *
  * Represents a strong profunctor over two **M**-modules, where
  *   - ⊘₁: **M** × **K₁** → **K₁** is the left action of **M** on **K₁**
  *   - ⊘₂: **M** × **K₂** → **K₂** is the left action of **M** on **K₂**
  *   - *τ*: *P*(*A*,*B*) → *P*(*C* ⊘₁ *A*,*C* ⊘₂ *B*) is the left strength
  */
abstract class Strong(
  tracked val P: Profunctor { val V: Total.type },
  tracked val L1: Module { val K: P.K1.type },
  tracked val L2: Module { val M: L1.M.type; val K: P.K2.type },
) extends caps.Pure {
  import P.P
  import P.K1.{Obj as Obj1, -->}
  import P.K2.{Obj as Obj2, --> as ->>}
  import L1.M.K.{Obj as ObjM, --> as ==>}
  import L1.`~` as `~1`
  import L2.`~` as `~2`

  /** The monoidal category acting on **K₁** and **K₂**. */
  val M: L1.M.type = L1.M
  import M.`*`

  /** The left strength *τ*: *P*(*A*,*B*) → *P*(*C* ⊘₁ *A*,*C* ⊘₂ *B*).
    */
  def left[A: Obj1, B: Obj2, C: ObjM](p: P[A, B]): P[C `~1` A, C `~2` B]

  extension [A: Obj1, B: Obj2](p: P[A, B]) {

    /** Postfix form of [[left]]. */
    @targetName("leftExt")
    final def left[C: ObjM]: P[C `~1` A, C `~2` B] = {
      Strong.this.left[A, B, C](p)
    }
  }

  /** Laws that any `Strong` profunctor must satisfy.
    *
    * The left strength is natural in *A* and *B*, dinatural in *C*, and compatible with the unitors and associators of
    * the actions.
    */
  object StrongLaws {

    /** *τ*(*P*(*f*,*g*)(*p*)) = *P*(*id* ⊘₁ *f*,*id* ⊘₂ *g*)(*τ*(*p*))
      */
    def naturality[A1: Obj1, B1: Obj2, A2: Obj1, B2: Obj2, C: ObjM](
      p: P[A1, B1],
      f: A2 --> A1,
      g: B1 ->> B2,
    )(using P[C `~1` A2, C `~2` B2] is Observable): Boolean = {
      left[A2, B2, C](P.dimap(f, g)(p)) =?=
        P.dimap(L1.act(M.K.identity[C], f), L2.act(M.K.identity[C], g))(left[A1, B1, C](p))
    }

    /** *P*(*h* ⊘₁ *id*,*id*)(*τ*(*p*)) = *P*(*id*,*h* ⊘₂ *id*)(*τ*(*p*)), dinaturality in *C*
      */
    def dinaturality[A: Obj1, B: Obj2, C1: ObjM, C2: ObjM](p: P[A, B], h: C1 ==> C2)(
      using P[C1 `~1` A, C2 `~2` B] is Observable
    ): Boolean = {
      P.dimap(L1.act(h, P.K1.identity[A]), P.K2.identity[C2 `~2` B])(left[A, B, C2](p)) =?=
        P.dimap(P.K1.identity[C1 `~1` A], L2.act(h, P.K2.identity[B]))(left[A, B, C1](p))
    }

    /** *P*(*λ*₁⁻¹,*λ*₂)(*τ*(*p*)) = *p*
      */
    def unitality[A: Obj1, B: Obj2](p: P[A, B])(using P[A, B] is Observable): Boolean = {
      P.dimap(L1.leftUnitor[A].from, L2.leftUnitor[B].to)(left[A, B, M.I](p)) =?= p
    }

    /** *P*(*α*₁,*α*₂⁻¹)(*τ*(*τ*(*p*))) = *τ*(*p*)
      */
    def associativity[A: Obj1, B: Obj2, C: ObjM, D: ObjM](p: P[A, B])(
      using P[(C * D) `~1` A, (C * D) `~2` B] is Observable
    ): Boolean = {
      P.dimap(L1.associator[C, D, A].to, L2.associator[C, D, B].from)(
        left[D `~1` A, D `~2` B, C](left[A, B, D](p))
      ) =?= left[A, B, C * D](p)
    }

    /** If *p* = *p*′, then *τ*(*p*) = *τ*(*p*′).
      *
      * @note The premise is not checked: *p*′ must be equal to *p* by construction.
      */
    def leftCongruence[A: Obj1, B: Obj2, C: ObjM](p: P[A, B], p2: P[A, B])(
      using P[C `~1` A, C `~2` B] is Observable
    ): Boolean = {
      left[A, B, C](p) =?= left[A, B, C](p2)
    }
  }
}

object Strong {

  /** A bistrong profunctor *P*: **K**ᵒᵖ × **K** → 𝒮 over a symmetric monoidal category **M** acting on itself.
    *
    * Represents a bistrong profunctor over the self-action of **M**, where
    *   - ⊗: **K** × **K** → **K** is the tensor of **M**, which acts on **K** from both sides
    *   - *τ*: *P*(*A*,*B*) → *P*(*C* ⊗ *A*,*C* ⊗ *B*) is the left strength
    *   - *τ*′: *P*(*A*,*B*) → *P*(*A* ⊗ *C*,*B* ⊗ *C*) is the right strength derived from the left strength
    *
    * Here, the action is ⊗ itself because a right strength needs a right action, which a left module does not have.
    */
  abstract class Bistrong(
    tracked override val P: Profunctor { val V: Total.type; val K2: K1.type },
    tracked override val M: Symmetric { val K: P.K1.type },
  ) extends Strong(P, Module.OfMonoidal(M), Module.OfMonoidal(M)) {
    import M.{`*`, given}
    import P.P
    import M.K.Obj

    /** The right strength *τ*′: *P*(*A*,*B*) → *P*(*A* ⊗ *C*,*B* ⊗ *C*).
      *
      * The right strength is derived from the left strength as *P*(*β*,*β*)(*τ*(*p*)).
      */
    def right[A: Obj, B: Obj, C: Obj](p: P[A, B]): P[A * C, B * C] = {
      P.dimap(M.braid[A, C], M.braid[C, B])(left[A, B, C](p))
    }

    extension [A: Obj, B: Obj](p: P[A, B]) {

      /** Postfix form of [[right]]. */
      @targetName("rightExt")
      final def right[C: Obj]: P[A * C, B * C] = {
        Bistrong.this.right[A, B, C](p)
      }
    }

    /** Laws that any `Bistrong` profunctor must satisfy.
      *
      * The left and the right strength commute, up to the associator.
      */
    object BistrongLaws {

      /** *τ*′(*τ*(*p*)) = *P*(*α*,*α*⁻¹)(*τ*(*τ*′(*p*)))
        */
      def compatibility[A: Obj, B: Obj, C: Obj, D: Obj](p: P[A, B])(
        using P[(C * A) * D, (C * B) * D] is Observable
      ): Boolean = {
        right[C * A, C * B, D](left[A, B, C](p)) =?=
          P.dimap(M.associator[C, A, D].to, M.associator[C, B, D].from)(
            left[A * D, B * D, C](right[A, B, D](p))
          )
      }
    }
  }

  object Bistrong {

    /** The bistrong structures on the profunctor *Q*: refines the profunctor, so that the profunctor of a strength *S*
      * is known as *Q*.
      */
    type On[Q <: Profunctor] = Bistrong { val P: Q }

    /** The opposite *P*ᵒᵖ of a bistrong promonad *P*, over **M**ᵒᵖ.
      *
      * The opposite has the same left strength, with every morphism reversed.
      *
      * @note **M** is meant to be `S.M.op`; its braiding is not checked.
      */
    final class Op(
      tracked val S: Bistrong { val P: Promonad },
      tracked override val M: Symmetric { val K: S.P.K.op.type; val T: Bifunctor { type Self = S.M.T.F } },
    ) extends Bistrong(Promonad.Op(S.P), M) {
      import M.`*`
      import P.P
      import P.K.Obj

      def left[A: Obj, B: Obj, C: Obj](p: P[A, B]): P[C * A, C * B] = {
        S.left[B, A, C](p)
      }
    }

    /** The bistrong hom promonad of a symmetric monoidal category **M**: *τ*(*f*) = *id* ⊗ *f*.
      *
      * Every symmetric monoidal category is bistrong over itself in this way.
      */
    open class Hom(tracked override val P: Promonad.Hom, tracked override val M: Symmetric { val K: P.K.type })
        extends Bistrong(P, M) {
      import M.`*`
      import P.K.{Obj, -->}

      def left[A: Obj, B: Obj, C: Obj](p: A --> B): (C * A) --> (C * B) = {
        M.tensor(P.K.identity[C], p)
      }
    }
  }
}
