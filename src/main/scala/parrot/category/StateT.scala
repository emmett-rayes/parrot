package parrot
package category

import scala.annotation.unused

/** A measure on a type of states: a natural number that guarded iteration and recursion must decrease.
  *
  * For a parser the state is the remaining input and its measure is its length: a loop step or a recursive call that
  * consumes input makes progress, and since the measure cannot decrease forever, guarded computations stop.
  */
trait Measure extends Type {

  /** The size of *s*, a natural number. */
  def measure(s: Self): Int
}

/** The state monad transformer: computations that read and update a state *S*, with the effects of a monad *M* on 𝒮.
  *
  * Represents a monad *T* on 𝒮, where
  *   - *T*[*A*] = *S* → *M*[*A* × *S*] ([[StateT.FunctorOf]])
  *   - *η*(*a*) = *s* ↦ *η*′(*a*,*s*)
  *   - *μ*(*m*) = *s* ↦ (((*n*,*s*′) ↦ *n*(*s*′))\*′)(*m*(*s*)): run the outer computation, then the inner one from the
  *     state it left
  *
  * It is the monad of the adjunction (− × *S*) ⊣ (*S* ⇒ −), with the effects of *M* in between.
  */
open class StateT[S](tracked val M: Monad.On[Total.type]) extends Monad(StateT.FunctorOf[S](M)) {

  def unit[A: Type]: A -> S -> M.M[(A, S)] = {
    a => s => M.unit[(A, S)]((a, s))
  }

  def flatten[A: Type]: (S -> M.M[(S -> M.M[(A, S)], S)]) -> S -> M.M[(A, S)] = {
    m => s => M.bind[(S -> M.M[(A, S)], S), (A, S)]((n, s2) => n(s2))(m(s))
  }
}

object StateT {

  /** The endofunctor of the state transformer: *S* → *M*[− × *S*], which maps the result and keeps the state. */
  final class FunctorOf[S](tracked val M: Monad.On[Total.type]) extends Endofunctor(Total) {
    type Self[A] = S -> M.M[(A, S)]

    def objects[A: Type]: (S -> M.M[(A, S)]) is Type = {
      Type.TIsType
    }

    def map[A: Type, B: Type](f: A -> B): (S -> M.M[(A, S)]) -> S -> M.M[(B, S)] = {
      m => s => M.map[(A, S), (B, S)]((a, s2) => (f(a), s2))(m(s))
    }
  }

  /** A classical structure on *M* lifts to the state transformer, where
    *   - *m̄* and *m̄*ᶜ keep the state they started with: they test without consuming
    *   - *m* ⊳ *n* runs *n* from the original state where *m* fails: it backtracks
    *   - *attempt*(*m*) keeps the new state on success and the original state on failure
    */
  open class ClassicalOf[S](tracked val T: StateT[S], tracked val R: ClassicalMonad { val M: T.M.type })
      extends ClassicalMonad(T) {

    def restrict[A](m: S -> T.M.M[(A, S)]): S -> T.M.M[(Unit, S)] = {
      s => T.M.map[Unit, (Unit, S)](_ => ((), s))(R.restrict(m(s)))
    }

    def zero[A]: S -> T.M.M[(A, S)] = {
      _ => R.zero
    }

    def complement[A](m: S -> T.M.M[(A, S)]): S -> T.M.M[(Unit, S)] = {
      s => T.M.map[Unit, (Unit, S)](_ => ((), s))(R.complement(m(s)))
    }

    def orElse[A](m: S -> T.M.M[(A, S)], n: -> S -> T.M.M[(A, S)]): S -> T.M.M[(A, S)] = {
      s => R.orElse(m(s), n(s))
    }

    override def attempt[A](m: S -> T.M.M[(A, S)]): S -> T.M.M[(Option[A], S)] = {
      s =>
        T.M.map[Option[(A, S)], (Option[A], S)] {
          case Some((a, s2)) => (Some(a), s2)
          case None          => (None, s)
        }(R.attempt(m(s)))
    }
  }

  /** Guarded iteration for the state transformer over a classical monad, where
    *   - *f*† runs *f* while it returns *X*, and fails as soon as a step returns *X* without decreasing the measure of
    *     the state
    *
    * Every run stops, since the measure cannot decrease forever. For guarded *f*, whose steps returning *X* always
    * decrease the measure, *f*† is the iteration of *f* and satisfies the laws of [[Elgot]].
    */
  open class GuardedIteration[S](tracked val T: StateT[S], tracked val R: ClassicalMonad { val M: T.M.type })(
    using size: S is Measure
  ) extends ElgotMonad(T) {

    def iterate[A, X](f: X -> S -> T.M.M[(Either[A, X], S)]): X -> S -> T.M.M[(A, S)] = {
      def loop(x: X, s: S): T.M.M[(A, S)] = {
        T.M.bind[(Either[A, X], S), (A, S)] {
          case (Left(a), s2)                                         => T.M.unit[(A, S)]((a, s2))
          case (Right(x2), s2) if size.measure(s2) < size.measure(s) => loop(x2, s2)
          case _                                                     => R.zero
        }(f(x)(s))
      }
      x => s => loop(x, s)
    }
  }

  /** Guarded recursion for the Kleisli arrows of the state transformer over a classical monad, where
    *   - *fix*(*f*) runs *f* applied to itself, and a call of the argument fails unless the measure of the state has
    *     decreased since the enclosing call began
    *
    * Every run stops, since the nesting of calls is bounded by the measure. For guarded *f*, which call their argument
    * only after decreasing the measure, *fix*(*f*) = *f*(*fix*(*f*)). A left-recursive *f* calls its argument without
    * progress, so that call fails: its other alternatives still run. The arrows of a family share the bound, so a call
    * of any of them must follow progress since the enclosing call of any other.
    */
  open class GuardedRecursion[S](
    tracked override val P: Kleisli { val M: StateT[S] },
    tracked val R: ClassicalMonad { val M: P.M.M.type },
  )(using size: S is Measure)
      extends Recursion(P) {

    def fix[A: Type, B: Type](f: (A -> S -> P.M.M.M[(B, S)]) -> (A -> S -> P.M.M.M[(B, S)]))
      : A -> S -> P.M.M.M[(B, S)] = {
      def knot(bound: Int): A -> S -> P.M.M.M[(B, S)] = {
        a => s =>
          val m = size.measure(s)
          if m < bound then f(knot(m))(a)(s) else R.zero
      }
      knot(Int.MaxValue)
    }

    def fixFamily[A: Type, B: Type](@unused n: Int)(
      f: (Int -> A -> S -> P.M.M.M[(B, S)]) -> Int -> A -> S -> P.M.M.M[(B, S)]
    ): Int -> A -> S -> P.M.M.M[(B, S)] = {
      def knots(bound: Int): Int -> A -> S -> P.M.M.M[(B, S)] = {
        i => a => s =>
          val m = size.measure(s)
          if m < bound then f(knots(m))(i)(a)(s) else R.zero
      }
      knots(Int.MaxValue)
    }
  }
}
