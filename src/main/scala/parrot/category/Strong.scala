package parrot
package category

import scala.annotation.targetName

/** A strength on a profunctor *P* valued in 𝒮, over a symmetric monoidal structure ⊗ on its base **K**: arrows can be
  * run on one side of a tensor while the other side is passed along.
  *
  * Represents a Tambara module, where
  *   - *first*: *P*(*A*,*B*) → *P*(*A* ⊗ *C*,*B* ⊗ *C*), natural in *A* and *B* and dinatural in *C*
  *   - *second*: *P*(*A*,*B*) → *P*(*C* ⊗ *A*,*C* ⊗ *B*) = *P*(*β*,*β*) ∘ *first*
  *
  * With ⊗ the product this is the *first* of arrows; with ⊗ the coproduct it is their *left*, often called *choice*. A
  * strong promonad whose *unit* and *multiply* preserve the strength is a Freyd category, see [[Freyd]].
  */
abstract class Strong(tracked val P: Profunctor { val V: Total.type }, tracked val M: Symmetric { val K: P.K.type })
    extends caps.Pure {
  import M.{*, given}
  import P.P
  import P.K.{Obj, -->}

  /** *first*: *P*(*A*,*B*) → *P*(*A* ⊗ *C*,*B* ⊗ *C*).
    */
  def first[A: Obj, B: Obj, C: Obj](p: P[A, B]): P[A * C, B * C]

  /** *second*: *P*(*A*,*B*) → *P*(*C* ⊗ *A*,*C* ⊗ *B*), by default *P*(*β*,*β*)(*first*(*p*)).
    */
  def second[A: Obj, B: Obj, C: Obj](p: P[A, B]): P[C * A, C * B] = {
    P.dimap(M.braid[C, A], M.braid[B, C])(first[A, B, C](p))
  }

  extension [A: Obj, B: Obj](p: P[A, B]) {

    /** Postfix form of [[first]]. */
    @targetName("firstExt")
    final def first[C: Obj]: P[A * C, B * C] = {
      Strong.this.first[A, B, C](p)
    }

    /** Postfix form of [[second]]. */
    @targetName("secondExt")
    final def second[C: Obj]: P[C * A, C * B] = {
      Strong.this.second[A, B, C](p)
    }
  }

  /** Laws that any `Strong` profunctor must satisfy. */
  object StrongLaws {

    /** *first*(*P*(*f*,*g*)(*p*)) = *P*(*f* ⊗ *id*,*g* ⊗ *id*)(*first*(*p*))
      */
    def naturality[A: Obj, B: Obj, A2: Obj, B2: Obj, C: Obj](
      p: P[A, B],
      f: A2 --> A,
      g: B --> B2,
    )(using P[A2 * C, B2 * C] is Observable): Boolean = {
      first[A2, B2, C](P.dimap(f, g)(p)) =?=
        P.dimap(M.tensor(f, P.K.identity[C]), M.tensor(g, P.K.identity[C]))(first[A, B, C](p))
    }

    /** *P*(*id* ⊗ *h*,*id*)(*first*(*p*)) = *P*(*id*,*id* ⊗ *h*)(*first*(*p*)), dinaturality in *C*
      */
    def dinaturality[A: Obj, B: Obj, C: Obj, C2: Obj](p: P[A, B], h: C --> C2)(
      using P[A * C, B * C2] is Observable
    ): Boolean = {
      P.dimap(M.tensor(P.K.identity[A], h), P.K.identity[B * C2])(first[A, B, C2](p)) =?=
        P.dimap(P.K.identity[A * C], M.tensor(P.K.identity[B], h))(first[A, B, C](p))
    }

    /** *P*(*ρ*⁻¹,*ρ*)(*first*(*p*)) = *p*
      */
    def unitality[A: Obj, B: Obj](p: P[A, B])(using P[A, B] is Observable): Boolean = {
      P.dimap(M.rightUnitor[A].from, M.rightUnitor[B].to)(first[A, B, I](p)) =?= p
    }

    /** *P*(*α*⁻¹,*α*)(*first*(*first*(*p*))) = *first*(*p*)
      */
    def associativity[A: Obj, B: Obj, C: Obj, D: Obj](p: P[A, B])(
      using P[A * (C * D), B * (C * D)] is Observable
    ): Boolean = {
      P.dimap(M.associator[A, C, D].from, M.associator[B, C, D].to)(first[A * C, B * C, D](first[A, B, C](p))) =?=
        first[A, B, C * D](p)
    }

    /** *second*(*p*) = *P*(*β*,*β*)(*first*(*p*))
      */
    def secondByBraiding[A: Obj, B: Obj, C: Obj](p: P[A, B])(
      using P[C * A, C * B] is Observable
    ): Boolean = {
      second[A, B, C](p) =?= P.dimap(M.braid[C, A], M.braid[B, C])(first[A, B, C](p))
    }

    /** If *p* = *p*′, then *first*(*p*) = *first*(*p*′).
      *
      * @note The premise is not checked: *p*′ must be equal to *p* by construction.
      */
    def firstCongruence[A: Obj, B: Obj, C: Obj](p: P[A, B], p2: P[A, B])(
      using P[A * C, B * C] is Observable
    ): Boolean = {
      first[A, B, C](p) =?= first[A, B, C](p2)
    }
  }
}

object Strong {

  /** The strength of a promonad over coproducts, read in the opposite promonad: a strength over products of **K**ᵒᵖ.
    * *first* is unchanged: *P*(*B*,*A*) → *P*(*B* + *C*,*A* + *C*) is *P*ᵒᵖ(*A*,*B*) → *P*ᵒᵖ(*A* × *C*,*B* × *C*).
    */
  final class OpOfCoproduct(tracked val S: Strong { val P: Promonad; val M: Cocartesian })
      extends Strong(Promonad.Op(S.P), Cocartesian.Op(S.M)) {
    import M.*
    import P.P
    import P.K.Obj

    def first[A: Obj, B: Obj, C: Obj](p: P[A, B]): P[A * C, B * C] = {
      S.first[B, A, C](p)
    }
  }

  /** The strength of a promonad over products, read in the opposite promonad: a strength over coproducts of **K**ᵒᵖ.
    */
  final class OpOfProduct(tracked val S: Strong { val P: Promonad; val M: Cartesian })
      extends Strong(Promonad.Op(S.P), Cartesian.Op(S.M)) {
    import M.*
    import P.P
    import P.K.Obj

    def first[A: Obj, B: Obj, C: Obj](p: P[A, B]): P[A * C, B * C] = {
      S.first[B, A, C](p)
    }
  }

  /** The strength of a hom promonad: *first*(*f*) = *f* ⊗ *id*. Every symmetric monoidal category is strong over itself
    * in this way.
    */
  open class OfHom(tracked override val P: Promonad.Hom, tracked override val M: Symmetric { val K: P.K.type })
      extends Strong(P, M) {
    import M.*
    import P.K.{Obj, -->}

    def first[A: Obj, B: Obj, C: Obj](p: A --> B): (A * C) --> (B * C) = {
      M.tensor(p, P.K.identity[C])
    }
  }
}
