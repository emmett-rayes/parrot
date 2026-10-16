package parrot
package category

/** A type *F* with a fixed-point operator *fix*: *F* ^ *F* ~> *F* satisfying the Conway laws.
  *
  * `Fixed` is the unparameterized counterpart of a [[Conway]] promonad. In a cartesian closed category the two are
  * interdefinable:
  *   - *fix* = *ev*†: *F* ^ *F* ~> *F*, the dagger of evaluation
  *   - *p*† = Λ(*p*) ⨾ *fix*, the fixed point of the transpose of *p*: *X* ⊗ *F* ~> *F*
  *
  * In particular, the fixed point of an endomorphism *f*: *F* ~> *F* is (λ ⨾ *f*)† = ⌜*f*⌝ ⨾ *fix*: *I* ~> *F*, where
  * ⌜*f*⌝ = Λ(λ ⨾ *f*): *I* ~> *F* ^ *F* is the transpose (name) of *f*.
  */
trait Fixed {
  type Self
  final type F = Self

  type In[_, _]: {Cartesian as FixedInCartesian, Closed as FixedInClosed}
  type Exp[_, _]

  val InIsCartesian: In is Cartesian = FixedInCartesian
  val InIsClosed
    : In is Closed.`with`[InIsCartesian.I, InIsCartesian.Tensor, Exp] { val SelfIsMonoidal: InIsCartesian.type }

  import InIsCartesian.*
  import InIsCartesian.SelfIsPromonad.*
  import InIsClosed.*

  /** The fixed-point operator *fix*: *F* ^ *F* ~> *F*. */
  def fix: (F ^ F) ~> F

  /** Maps a morphism *p*: *X* ⊗ *F* ~> *F* to the fixed point *p*† = Λ(*p*) ⨾ *fix*: *X* ~> *F* of its transpose
    * Λ(*p*): *X* ~> *F* ^ *F*.
    */
  def fixTr[X](p: (X * F) ~> F): X ~> F = {
    curry(p) >>> fix
  }

  /** Laws that any `Fixed` must satisfy, stated in terms of the fixed points *p*† = Λ(*p*) ⨾ *fix* of transposes.
    *
    * The laws are parameterized by an object *X*, since in a category that is not well-pointed the laws at global
    * elements *X* = *I* do not imply those at arbitrary *X*.
    */
  object FixedLaws {

    /** Fixed-point property (universal): *fix* = *ev* ∘ ⟨*id*, *fix*⟩ */
    def fixedPoint(using ((F ^ F) ~> F) is Eq): Boolean = {
      (identity[F ^ F] &&& fix) >>> eval === fix
    }

    /** Fixed-point property: *p*† = *p* ∘ ⟨*id*, *p*†⟩
      *
      * @note Follows from the universal fixed-point property, of which it is the instance along Λ(*p*).
      */
    def fixedPoint[X](p: (X * F) ~> F)(using (X ~> F) is Eq): Boolean = {
      fixTr(p) === (identity[X] &&& fixTr(p)) >>> p
    }

    /** Composition identity (dinaturality): (*g* ∘ *p*)† = *g* ∘ (*p* ∘ (*id* ⊗ *g*))† */
    def composition[X, G](p: (X * F) ~> G, g: G ~> F)(using
      G: G is Fixed.in[In, I, Tensor, Exp],
      eq: (X ~> F) is Eq,
    ): Boolean = {
      fixTr(p >>> g) === G.fixTr((identity[X] *** g) >>> p) >>> g
    }

    /** Double dagger identity (diagonality / Bekić): (*p* ∘ ⟨*id*, π₂⟩)† = (*p*†)† */
    def doubleDagger[X](p: ((X * F) * F) ~> F)(using (X ~> F) is Eq): Boolean = {
      fixTr((identity[X * F] &&& second[X, F]) >>> p) === fixTr(fixTr(p))
    }
  }
}

object Fixed {

  /** Refines the `In` type of `Fixed` to the cartesian closed `K` with terminal `U`, product `T`, and exponential `E`.
    */
  type in[K[_, _], U, T[_, _], E[_, _]] = Fixed {
    type In  = K
    type Exp = E
    val InIsCartesian: K is Cartesian.`with`[U, T]
    val InIsClosed: K is Closed.`with`[U, T, E]
  }

  /** Summons the `Fixed` instance of `F`. */
  def apply[F: Fixed]: F is Fixed = summon

  /** The fixed-point operator *fix*: *Exp*[*X*, *X*] ~> *X* on an exponential *X* = *Exp*[*A*, *B*] of a cartesian
    * closed category with a Conway operator.
    *
    * @note Rather than the dagger of evaluation *ev*†, this is the dagger of its η-expansion *ev* ∘ ⟨π₁, Λ(*ev* ∘ (π₂ ⊗
    *   *id*))⟩, which is equal by the η law but productive under strict evaluation: the fixed point is passed on as a
    *   new exponential that only unfolds the knot when applied.
    * @note The monoidal structure of `L` is required to be the cartesian structure of `K`, so that the dagger,
    *   currying, and evaluation agree on the products.
    */
  given ExponentialIsFixed: [P[_, _], U, T[_, _], E[_, _], A, B] => (
    K: P is Conway.`with`[U, T],
    L: P is Closed.`with`[U, T, E] { val SelfIsMonoidal: K.SelfIsCartesian.type },
  ) => (E[A, B] is Fixed.in[P, U, T, E]) = new Fixed {
    type Self = E[A, B]
    type In   = P
    type Exp  = E

    override given FixedInCartesian: K.SelfIsCartesian.type = K.SelfIsCartesian
    override given FixedInClosed: L.type                    = L
    override val InIsCartesian: K.SelfIsCartesian.type      = K.SelfIsCartesian
    override val InIsClosed: L.type                         = L

    import InIsCartesian.SelfIsPromonad.*
    import InIsClosed.*

    def fix: (F ^ F) ~> F = {
      import K.*
      import K.SelfIsCartesian.*
      import K.SelfIsCartesian.SelfIsPromonad.*
      import L.*
      type X = B ^ A
      val unfold: ((X ^ X) * X * A) ~> B = (second *** identity) >>> eval
      val delayed: ((X ^ X) * X) ~> X    = curry(unfold)
      val knot: ((X ^ X) * X) ~> X       = (first &&& delayed) >>> eval
      dagger(knot)
    }
  }

  /** `A => B` has fixed points as an exponential of the cartesian closed category **Type** with lazy products, derived
    * from the knot-tying Conway operator on `Function`: *fix*(*f*) = *g* where *g* = *f*(*a* ↦ *g*(*a*)).
    */
  given FunctionIsFixed: [A, B] => (Function[A, B] is Fixed.in[Function, Unit, LazyTuple2, Function]) =
    ExponentialIsFixed[Function, Unit, LazyTuple2, Function, A, B](
      using
      Conway.FunctionIsLazyCartesianConway,
      Closed.FunctionIsLazyClosed,
    )

  /** `(A, B)` has fixed points as an object of the cartesian closed category **Type** with lazy products if `A` and `B`
    * do, by Bekić's theorem:
    *
    * *fix*(*f*) = (*a*₀, *b*₀) where *b*₀ = *fix*(*b* ↦ *f*₂(*a*(*b*), *b*)), *a*₀ = *a*(*b*₀) and *a*(*b*) = \
    * *fix*(*a* ↦ *f*₁(*a*, *b*)).
    */
  given Tuple2IsFixed: [A, B] => (
    FA: A is Fixed.in[Function, Unit, LazyTuple2, Function],
    FB: B is Fixed.in[Function, Unit, LazyTuple2, Function],
  ) => ((A, B) is Fixed.in[Function, Unit, LazyTuple2, Function]) = new Fixed {
    type Self = (A, B)
    type In   = Function
    type Exp  = Function

    override given FixedInCartesian: Cartesian.FunctionIsLazyCartesian.type = Cartesian.FunctionIsLazyCartesian
    override given FixedInClosed: Closed.FunctionIsLazyClosed.type          = Closed.FunctionIsLazyClosed
    override val InIsCartesian: Cartesian.FunctionIsLazyCartesian.type      = Cartesian.FunctionIsLazyCartesian
    override val InIsClosed: Closed.FunctionIsLazyClosed.type               = Closed.FunctionIsLazyClosed

    import InIsCartesian.SelfIsPromonad.*
    import InIsClosed.*

    def fix: (F ^ F) ~> F = { f =>
      def solveFirst(b: B): A = FA.fix(a => f((a, b))._1)
      val b0: B               = FB.fix(b => f((solveFirst(b), b))._2)
      (solveFirst(b0), b0)
    }
  }
}
