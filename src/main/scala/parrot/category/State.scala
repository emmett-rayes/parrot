package parrot
package category

import scala.annotation.unused

import Category.Type

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
  * It is the monad of the adjunction (− × *S*) ⊣ (*S* ⇒ −), with the effects of *M* in between. Over the identity, it
  * is the state monad, [[State]].
  */
open class StateT[S](tracked val monad: Monad.On[Total.type]) extends Monad(StateT.FunctorOf[S](monad)) {

  def unit[A: Type]: A -> S -> monad.M[(A, S)] = {
    a => s => monad.unit[(A, S)]((a, s))
  }

  def flatten[A: Type]: (S -> monad.M[(S -> monad.M[(A, S)], S)]) -> S -> monad.M[(A, S)] = {
    m => s => monad.bind[(S -> monad.M[(A, S)], S), (A, S)]((n, s2) => n(s2))(m(s))
  }
}

object StateT {

  /** The endofunctor of the state transformer: *S* → *M*[− × *S*], which maps the result and keeps the state. */
  final class FunctorOf[S](tracked val monad: Monad.On[Total.type]) extends Endofunctor(Total) {
    type Self[A] = S -> monad.M[(A, S)]

    def objects[A: Type]: (S -> monad.M[(A, S)]) is Type = {
      Type.TIsType
    }

    def map[A: Type, B: Type](f: A -> B): (S -> monad.M[(A, S)]) -> S -> monad.M[(B, S)] = {
      m => s => monad.map[(A, S), (B, S)]((a, s2) => (f(a), s2))(m(s))
    }
  }

  /** A classical structure on *M* lifts to the state transformer, where
    *   - *m̄* and *m̄*ᶜ keep the state they started with: they test without consuming
    *   - *m* ⊳ *n* runs *n* from the original state where *m* fails: it backtracks
    *   - *attempt*(*m*) keeps the new state on success and the original state on failure
    */
  open class ClassicalOf[S](
    tracked val transformer: StateT[S],
    tracked val classical: Monad.Classical { val monad: transformer.monad.type },
  ) extends Monad.Classical(transformer) {
    import transformer.monad.M

    def restrict[A](m: S -> M[(A, S)]): S -> M[(Unit, S)] = {
      s => transformer.monad.map[Unit, (Unit, S)](_ => ((), s))(classical.restrict(m(s)))
    }

    def zero[A]: S -> M[(A, S)] = {
      _ => classical.zero
    }

    def complement[A](m: S -> M[(A, S)]): S -> M[(Unit, S)] = {
      s => transformer.monad.map[Unit, (Unit, S)](_ => ((), s))(classical.complement(m(s)))
    }

    def orElse[A](m: S -> M[(A, S)], n: -> S -> M[(A, S)]): S -> M[(A, S)] = {
      s => classical.orElse(m(s), n(s))
    }

    override def attempt[A](m: S -> M[(A, S)]): S -> M[(Option[A], S)] = {
      s =>
        transformer.monad.map[Option[(A, S)], (Option[A], S)] {
          case Some((a, s2)) => (Some(a), s2)
          case None          => (None, s)
        }(classical.attempt(m(s)))
    }
  }

  /** Guarded iteration for the state transformer over a classical monad, where
    *   - *f*† runs *f* while it returns *X*, and fails as soon as a step returns *X* without decreasing the measure of
    *     the state
    *
    * Every run stops, since the measure cannot decrease forever. For guarded *f*, whose steps returning *X* always
    * decrease the measure, *f*† is the iteration of *f* and satisfies the laws of [[Elgot]].
    */
  open class GuardedIteration[S](
    tracked val transformer: StateT[S],
    tracked val classical: Monad.Classical { val monad: transformer.monad.type },
  )(using size: S is Measure)
      extends Monad.Elgot(transformer) {
    import transformer.monad.M

    def iterate[A, X](f: X -> S -> M[(Either[A, X], S)]): X -> S -> M[(A, S)] = {
      def loop(x: X, s: S): M[(A, S)] = {
        transformer.monad.bind[(Either[A, X], S), (A, S)] {
          case (Left(a), s2)                                         => transformer.monad.unit[(A, S)]((a, s2))
          case (Right(x2), s2) if size.measure(s2) < size.measure(s) => loop(x2, s2)
          case _                                                     => classical.zero
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
    tracked override val promonad: Kleisli { val monad: StateT[S] },
    tracked val classical: Monad.Classical { val monad: promonad.monad.monad.type },
  )(using size: S is Measure)
      extends Recursion(promonad) {
    import promonad.monad.monad.M

    def fix[A: Type, B: Type](f: (A -> S -> M[(B, S)]) -> (A -> S -> M[(B, S)]))
      : A -> S -> M[(B, S)] = {
      def knot(bound: Int): A -> S -> M[(B, S)] = {
        a => s =>
          val m = size.measure(s)
          if m < bound then f(knot(m))(a)(s) else classical.zero
      }
      knot(Int.MaxValue)
    }

    def fixFamily[A: Type, B: Type](@unused n: Int)(
      f: (Int -> A -> S -> M[(B, S)]) -> Int -> A -> S -> M[(B, S)]
    ): Int -> A -> S -> M[(B, S)] = {
      def knots(bound: Int): Int -> A -> S -> M[(B, S)] = {
        i => a => s =>
          val m = size.measure(s)
          if m < bound then f(knots(m))(i)(a)(s) else classical.zero
      }
      knots(Int.MaxValue)
    }
  }
}

/** The state monad on 𝒮: computations that read and update a state *S*, the state transformer [[StateT]] over the
  * identity.
  *
  * Represents a monad on 𝒮, where
  *   - *M*[*A*] = *S* → *A* × *S*
  *   - *η*(*a*) = *s* ↦ (*a*,*s*)
  *   - *μ*(*m*) = *s* ↦ ((*n*,*s*′) ↦ *n*(*s*′))(*m*(*s*)): run the outer computation, then the inner one from the
  *     state it left
  */
open class State[S] extends StateT[S](Monad.Identity)
