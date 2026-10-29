package parrot
package category

/** An oracle for observational equality.
  *
  * Represents a test of equality, where
  *   - ≟ is a decidable equivalence relation that holds whenever the two values are equal
  *
  * Laws compare morphisms, and morphisms are usually functions, whose equality is not decidable. An `Observable`
  * decides something weaker: whether two values agree on finitely many observations, each ending in data that is
  * compared using equality. Data observes itself. A function is observed by applying it at sample points.
  *
  * @see [[Eq]] for equality on data.
  *
  * @note Agreement is coarser than equality: two values may agree on every observation without being equal. It is
  *   therefore sound for refutation only: a law that fails under some `Observable` is false, but a law that holds is
  *   not thereby proved.
  *
  * @note Agreement on samples is not a congruence: composites of agreeing functions can disagree. Congruence laws
  *   therefore take values that are assumed to be equal by construction, rather than values that agree on samples.
  */
trait Observable extends caps.Pure {
  type Self

  /** Returns `true` if *a* and *b* agree on every observation. */
  def agree(a: Self, b: Self): Boolean

  extension (a: Self)
    /** Infix extension for [[agree]]. */
    final def =?=(b: Self): Boolean = {
      Observable.this.agree(a, b)
    }

  /** Laws that any `Observable` must satisfy.
    *
    * Agreement is an equivalence relation, and equal values agree.
    */
  object ObservableLaws {
    extension (p: Boolean)
      private def implies(q: Boolean): Boolean = {
        !p || q
      }

    /** *a* ≟ *a*
      */
    def reflexivity(a: Self): Boolean = {
      a =?= a
    }

    /** If *a* ≟ *b*, then *b* ≟ *a* */
    def symmetry(a: Self, b: Self): Boolean = {
      (a =?= b) `implies` (b =?= a)
    }

    /** If *a* ≟ *b* and *b* ≟ *c*, then *a* ≟ *c* */
    def transitivity(a: Self, b: Self, c: Self): Boolean = {
      (a =?= b && b =?= c) `implies` (a =?= c)
    }

    /** If *a*₁ = *a*₂, then *a*₁ ≟ *a*₂
      *
      * @note The premise is not checked: *a*₂ must be equal to *a*₁ by construction.
      */
    def soundness(a1: Self, a2: Self): Boolean = {
      a1 =?= a2
    }
  }
}

/** Observability for pairs wherever the components are observable.
  *
  * @note Defined as a low-priority parent of the companion of [[Observable]], so that [[Observable.EqIsObservable]]
  *   takes precedence: for a pair of data, agreement is componentwise equality.
  */
trait ComponentwiseObservable {

  /** Observes a pair componentwise: two pairs agree when their first components agree and their second components do.
    */
  given Tuple2IsObservable: [A: Observable, B: Observable] => ((A, B) is Observable) {
    def agree(a: (A, B), b: (A, B)): Boolean = {
      (a._1 =?= b._1) && (a._2 =?= b._2)
    }
  }
}

object Observable extends ComponentwiseObservable {

  /** Summons the `Observable` instance of `A`. */
  def apply[A: Observable]: A is Observable = summon

  /** Data observes itself: two values agree when they are equal. */
  given EqIsObservable: [A: Eq] => A is Observable {
    def agree(a: A, b: A): Boolean = {
      a === b
    }
  }

  /** Observes a value through finitely many observations: two values agree when every observation agrees. */
  def through[A, O: Observable](observations: List[A -> O]): A is Observable = {
    new Observable {
      type Self = A

      def agree(a: A, b: A): Boolean = {
        observations.forall(o => o(a) =?= o(b))
      }
    }
  }

  /** Observes a total function by applying it at the given sample points. */
  def total[A, B: Observable](points: List[A]): (A -> B) is Observable = {
    through[A -> B, B](points.map(a => (f: A -> B) => f(a)))
  }

  /** Observes a partial function by applying it at the given sample points. */
  def partial[A, B: Observable](points: List[A]): (A ~> B) is Observable = {
    through[A ~> B, B](points.map(a => (f: A ~> B) => f.run(a)))
  }
}
