package parrot
package category

/** A type *M* with a fixed-point operator fix: (*M* → *M*) → *M* satisfying the Conway laws.
  *
  * `Fixed` is the unparameterized counterpart of a [[Conway]] promonad. In a cartesian closed category the two are
  * interdefinable:
  *   - fix = *ev*†: *Exp*[*M*, *M*] ~> *M*, the dagger of evaluation
  *   - *f*† = Λ(*f*) ⨾ fix, the fixed point of the transpose of *f*
  *
  * Not every type of **Type** has fixed points (e.g. `Int`), but exponentials do: see [[Fixed.exponential]].
  */
trait Fixed {
  type Self
  final type M = Self

  /** The fixed point of *f*. */
  def fix(f: M => M): M

  /** Laws that any `Fixed` must satisfy. */
  object FixedLaws {

    /** Fixed-point property: fix(*f*) = *f*(fix(*f*))
      */
    def fixedPoint(f: M => M)(using M is Eq): Boolean = {
      fix(f) === f(fix(f))
    }

    /** Dinaturality (composition identity): fix(*g* ∘ *f*) = *g*(fix(*f* ∘ *g*))
      */
    def dinaturality[N](f: M => N, g: N => M)(using N: N is Fixed, eq: M is Eq): Boolean = {
      fix(f.andThen(g)) === g(N.fix(g.andThen(f)))
    }

    /** Diagonal property: fix(*x* ↦ fix(*y* ↦ *f*(*x*, *y*))) = fix(*x* ↦ *f*(*x*, *x*))
      */
    def diagonal(f: (M, M) => M)(using M is Eq): Boolean = {
      fix(x => fix(y => f(x, y))) === fix(x => f(x, x))
    }
  }
}

object Fixed {

  /** Summons the `Fixed` instance of `M`. */
  def apply[M: Fixed]: M is Fixed = summon

  /** The fixed-point operator fix: *Exp*[*X*, *X*] ~> *X* on an exponential *X* = *Exp*[*A*, *B*] of a cartesian closed
    * category with a Conway operator.
    *
    * Rather than the dagger of evaluation *ev*†, this is the dagger of its η-expansion *ev* ∘ ⟨π₁, Λ(*ev* ∘ (π₂ ⊗
    * *id*))⟩, which is equal by the η law but productive under strict evaluation: the fixed point is passed on as a new
    * exponential that only unfolds the knot when applied.
    */
  def exponential[P[_, _], U, T[_, _], E[_, _], A, B](
    using
    K: P is Conway.`with`[U, T],
    L: P is Closed.`with`[U, T, E],
  ): P[E[E[A, B], E[A, B]], E[A, B]] = {
    import L.SelfIsCartesian.{&&&, ***, first, second}
    import L.SelfIsCartesian.SelfIsPromonad.{identity, >>>}
    type X = E[A, B]
    val unfold: P[T[T[E[X, X], X], A], B] = (second[E[X, X], X] *** identity[A]) >>> L.eval[A, B]
    val delayed: P[T[E[X, X], X], X]      = L.curry[A, B, T[E[X, X], X]](unfold)
    val knot: P[T[E[X, X], X], X]         = (first[E[X, X], X] &&& delayed) >>> L.eval[X, X]
    K.dagger[E[X, X], X](knot)
  }

  /** `A => B` has fixed points as an exponential of the cartesian closed category **Type** with lazy products, derived
    * from the knot-tying Conway operator on `Function`: fix(*f*) = *g* where *g* = *f*(*a* ↦ *g*(*a*)).
    *
    * This is the least fixed point with respect to non-termination: unguarded recursion diverges.
    */
  given FunctionIsFixed: [A, B] => Function[A, B] is Fixed {
    private val fixExponential: ((A => B) => (A => B)) => (A => B) = {
      exponential[Function, Unit, LazyTuple2, Function, A, B](
        using Conway.FunctionIsLazyCartesianConway,
        Closed.FunctionIsLazyClosed,
      )
    }

    def fix(f: (A => B) => (A => B)): A => B = fixExponential(f)
  }

  /** `(A, B)` has fixed points if `A` and `B` do, by Bekić's theorem:
    *
    * fix(*f*) = (*a*₀, *b*₀) where *b*₀ = fix(*b* ↦ *f*₂(*a*(*b*), *b*)), *a*₀ = *a*(*b*₀) and *a*(*b*) = fix(*a* ↦
    * *f*₁(*a*, *b*)).
    */
  given Tuple2IsFixed: [A, B] => (FA: A is Fixed, FB: B is Fixed) => (A, B) is Fixed {
    def fix(f: ((A, B)) => (A, B)): (A, B) = {
      def solveFirst(b: B): A = FA.fix(a => f((a, b))._1)
      val b0                  = FB.fix(b => f((solveFirst(b), b))._2)
      (solveFirst(b0), b0)
    }
  }
}
