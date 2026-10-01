package parrot
package category

import scala.annotation.targetName

/** A traced profunctor on an underlying monoidal category **C**.
  *
  * Represents a profunctor *P*: **C**^*op* × **C** → **Type** equipped with a tensorial trace (cotensorial strength)
  * with respect to a monoidal category (**C**, ⊗, *I*), where
  *   - *left*: *P*[*A* ⊗ *C*, *B* ⊗ *C*] → *P*[*A*, *B*] is the left trace
  *   - *right*: *P*[*C* ⊗ *A*, *C* ⊗ *B*] → *P*[*A*, *B*] is the right trace
  */
trait Traced extends Profunctor {
  type Self[_, _]

  override type On[_, _]: Monoidal

  val Mon: On is Monoidal = summon
  import Mon.*

  /** Left tensorial trace: *P*[*A* ⊗ *C*, *B* ⊗ *C*] → *P*[*A*, *B*]. */
  def left[A, B, C](p: (A * C) ~> (B * C)): A ~> B

  /** Right tensorial trace: *P*[*C* ⊗ *A*, *C* ⊗ *B*] → *P*[*A*, *B*]. */
  def right[A, B, C](p: (C * A) ~> (C * B)): A ~> B

  extension [A, B, C](p: (A * C) ~> (B * C))
    /** Infix extension for [[left]]. */
    @targetName("leftExt")
    def left(using DummyImplicit): A ~> B = {
      Traced.this.left(p)
    }

  extension [C, A, B](p: (C * A) ~> (C * B))
    /** Infix extension for [[right]]. */
    @targetName("rightExt")
    def right(using DummyImplicit): A ~> B = {
      Traced.this.right(p)
    }

  /** Laws that any `Traced` profunctor must satisfy. */
  object TracedLaws {

    /** *left*(*P*(*f* ⊗ *id*, *g* ⊗ *id*)(*p*)) = *P*(*f*, *g*)(*left*(*p*))
      */
    def leftNaturality[A, B, C, D, X](p: (A * X) ~> (B * X), f: C ==> A, g: B ==> D)(
      using C ~> D is Eq
    ): Boolean = {
      p.dimap(f *** Promonad[On].identity[X], g *** Promonad[On].identity[X]).left === p.left.dimap(f, g)
    }

    /** *right*(*P*(*id* ⊗ *f*, *id* ⊗ *g*)(*p*)) = *P*(*f*, *g*)(*right*(*p*))
      */
    def rightNaturality[A, B, C, D, X](p: (X * A) ~> (X * B), f: C ==> A, g: B ==> D)(
      using C ~> D is Eq
    ): Boolean = {
      p.dimap(Promonad[On].identity[X] *** f, Promonad[On].identity[X] *** g).right === p.right.dimap(f, g)
    }

    /** *left*(*P*(ρ, ρ⁻¹)(*p*)) = *p*
      */
    def leftUnitality[A, B](p: A ~> B)(
      using A ~> B is Eq
    ): Boolean = {
      p.dimap(rightUnitor[A], rightUnitorInv[B]).left === p
    }

    /** *right*(*P*(λ, λ⁻¹)(*p*)) = *p*
      */
    def rightUnitality[A, B](p: A ~> B)(
      using A ~> B is Eq
    ): Boolean = {
      p.dimap(leftUnitor[A], leftUnitorInv[B]).right === p
    }

    /** *left*(*left*(*p*)) = *left*(*P*(α⁻¹, α)(*p*))
      */
    def leftAssociativity[A, B, C, D](p: ((A * C) * D) ~> ((B * C) * D))(
      using A ~> B is Eq
    ): Boolean = {
      p.left.left === p.dimap(unassociate[A, C, D], associate[B, C, D]).left
    }

    /** *right*(*right*(*p*)) = *right*(*P*(α, α⁻¹)(*p*))
      */
    def rightAssociativity[A, B, C, D](p: (D * (C * A)) ~> (D * (C * B)))(
      using A ~> B is Eq
    ): Boolean = {
      p.right.right === p.dimap(associate[D, C, A], unassociate[D, C, B]).right
    }
  }
}

object Traced {
  import Profunctor.on

  /** Summons the `Traced` instance of `P`. */
  def apply[P[_, _]: Traced]: P is Traced = summon

  /** `Function` is traced under its cartesian monoidal structure via fixed points. */
  given FunctionIsLazyCartesianTraced: (F: Function is Profunctor on Function) => Function is Traced {
    export F.{Self as _, *}

    override val Mon: Function is Monoidal.`with`[Unit, LazyTuple2] = Cartesian.FunctionIsLazyCartesian

    def left[A, B, C](p: LazyTuple2[A, C] => LazyTuple2[B, C]): A => B = {
      a =>
        {
          lazy val result: LazyTuple2[B, C] = p(LazyTuple2(a, result._2))
          result._1
        }
    }

    def right[A, B, C](p: LazyTuple2[C, A] => LazyTuple2[C, B]): A => B = {
      a =>
        {
          lazy val result: LazyTuple2[C, B] = p(LazyTuple2(result._1, a))
          result._2
        }
    }
  }

  /** `Function` is traced under its cocartesian monoidal structure via tail-recursive iteration. */
  given FunctionIsCocartesianTraced: (F: Function is Profunctor on Function) => (Function is Traced) {
    export F.{Self as _, *}

    override val Mon: Function is Monoidal.`with`[Nothing, Either] = Cocartesian.FunctionIsCocartesian

    def left[A, B, C](p: Either[A, C] => Either[B, C]): A => B = { a =>
      @annotation.tailrec
      def loop(curr: Either[A, C]): B = p(curr) match {
        case Left(b)  => b
        case Right(c) => loop(Right(c))
      }
      loop(Left(a))
    }

    def right[A, B, C](p: Either[C, A] => Either[C, B]): A => B = { a =>
      @annotation.tailrec
      def loop(curr: Either[C, A]): B = p(curr) match {
        case Right(b) => b
        case Left(c)  => loop(Left(c))
      }
      loop(Right(a))
    }
  }
}
