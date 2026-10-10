package parrot
package category

/** A cartesian closed structure on a category with finite products.
  *
  * Represents a promonad *P* whose induced category is cartesian (⊗, *I*) and has exponentials, where
  *   - *Exp*[*A*, *B*] is the exponential object *B*^*A*
  *   - *ev*: *Exp*[*A*, *B*] ⊗ *A* ~> *B* is evaluation
  *   - Λ: *P*[*C* ⊗ *A*, *B*] → *P*[*C*, *Exp*[*A*, *B*]] is currying, the transpose of the adjunction - ⊗ *A* ⊣
  *     *Exp*[*A*, -]
  */
trait Closed {
  type Self[_, _]: Cartesian

  val SelfIsCartesian: Self is Cartesian = summon
  import SelfIsCartesian.{***, `*`}
  import SelfIsCartesian.SelfIsPromonad.{identity, ~>, >>>}

  /** The exponential object *Exp*[*A*, *B*]. */
  type Exp[_, _]

  /** The evaluation morphism *ev*: *Exp*[*A*, *B*] ⊗ *A* ~> *B*. */
  def eval[A, B]: (Exp[A, B] * A) ~> B

  /** Maps a morphism *f*: *C* ⊗ *A* ~> *B* to its transpose Λ(*f*): *C* ~> *Exp*[*A*, *B*]. */
  def curry[A, B, C](f: (C * A) ~> B): C ~> Exp[A, B]

  /** Maps a morphism *g*: *C* ~> *Exp*[*A*, *B*] to its transpose *ev* ∘ (*g* ⊗ *id*): *C* ⊗ *A* ~> *B*. */
  def uncurry[A, B, C](g: C ~> Exp[A, B]): (C * A) ~> B = {
    (g *** identity[A]) >>> eval[A, B]
  }

  /** Laws that any `Closed` must satisfy. */
  object ClosedLaws {

    /** (β) *ev* ∘ (Λ(*f*) ⊗ *id*) = *f*
      */
    def beta[A, B, C](f: (C * A) ~> B)(using ((C * A) ~> B) is Eq): Boolean = {
      uncurry(curry(f)) === f
    }

    /** (η) Λ(*ev* ∘ (*g* ⊗ *id*)) = *g*
      */
    def eta[A, B, C](g: C ~> Exp[A, B])(using (C ~> Exp[A, B]) is Eq): Boolean = {
      curry(uncurry(g)) === g
    }
  }
}

object Closed {

  /** Refines the products of `Closed` to the unit `U` and product `T`, and its exponentials to `E`. */
  type `with`[U, T[_, _], E[_, _]] = Closed {
    val SelfIsCartesian: Cartesian.`with`[U, T]
    type Exp[A, B] = E[A, B]
  }

  /** Summons the `Closed` instance of `P`. */
  def apply[P[_, _]: Closed]: P is Closed = summon

  /** `Function` is cartesian closed under tuple products with function types as exponentials. */
  given FunctionIsClosed: Function is Closed {
    override given given_Cartesian_Self: Cartesian.FunctionIsCartesian.type = Cartesian.FunctionIsCartesian
    override val SelfIsCartesian: Cartesian.FunctionIsCartesian.type        = Cartesian.FunctionIsCartesian

    type Exp[A, B] = A => B

    def eval[A, B]: ((A => B, A)) => B = {
      (f, a) => f(a)
    }

    def curry[A, B, C](f: ((C, A)) => B): C => A => B = {
      c => a => f((c, a))
    }
  }

  /** `Function` is cartesian closed under lazy tuple products with function types as exponentials. */
  given FunctionIsLazyClosed: Function is Closed {
    override given given_Cartesian_Self: Cartesian.FunctionIsLazyCartesian.type = Cartesian.FunctionIsLazyCartesian
    override val SelfIsCartesian: Cartesian.FunctionIsLazyCartesian.type        = Cartesian.FunctionIsLazyCartesian

    type Exp[A, B] = A => B

    def eval[A, B]: LazyTuple2[A => B, A] => B = {
      p => p._1(p._2)
    }

    def curry[A, B, C](f: LazyTuple2[C, A] => B): C => A => B = {
      c => a => f(LazyTuple2(c, a))
    }
  }
}
