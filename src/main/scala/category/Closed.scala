package parrot
package category

/** A monoidal closed promonad on an underlying category **C**.
  *
  * Represents a promonad *P* whose induced category is monoidal with unit *I* and tensor ⊗ and has internal homs
  * (exponentials), where
  *   - *Exp*[*A*, *B*] is the internal hom object *B*^*A* (or [A, B])
  *   - *ev*: *Exp*[*A*, *B*] ⊗ *A* ~> *B* is evaluation
  *   - Λ: *P*[*C* ⊗ *A*, *B*] → *P*[*C*, *Exp*[*A*, *B*]] is currying
  */
trait Closed {
  type Self[_, _]: Monoidal as ClosedMonoidal

  val SelfIsMonoidal: Self is Monoidal = ClosedMonoidal
  import SelfIsMonoidal.*
  import SelfIsMonoidal.SelfIsPromonad.*

  /** The internal hom object *Exp*[*A*, *B*]. */
  type Exp[_, _]
  final type ^[B, A] = Exp[A, B]

  /** The evaluation morphism *ev*: *Exp*[*A*, *B*] ⊗ *A* ~> *B*. */
  def eval[A, B]: ((B ^ A) * A) ~> B

  /** Maps a morphism *f*: *C* ⊗ *A* ~> *B* to its transpose Λ(*f*): *C* ~> *Exp*[*A*, *B*]. */
  def curry[A, B, C](f: (C * A) ~> B): C ~> (B ^ A)

  /** Maps a morphism *g*: *C* ~> *Exp*[*A*, *B*] to its transpose *ev* ∘ (*g* ⊗ *id*): *C* ⊗ *A* ~> *B*. */
  def uncurry[A, B, C](g: C ~> (B ^ A)): (C * A) ~> B = {
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
    def eta[A, B, C](g: C ~> (B ^ A))(using (C ~> (B ^ A)) is Eq): Boolean = {
      curry(uncurry(g)) === g
    }
  }
}

object Closed {

  /** Refines the tensor of `Closed` to the unit `U` and tensor `T`, and its exponentials to `E`. */
  type `with`[U, T[_, _], E[_, _]] = Closed {
    type Exp = E
    val SelfIsMonoidal: Monoidal.`with`[U, T]
  }

  /** Summons the `Closed` instance of `P`. */
  def apply[P[_, _]: Closed]: P is Closed = summon

  /** `Function` is monoidal closed under tuple products with function types as exponentials. */
  given FunctionIsClosed: Function is Closed {
    override given ClosedMonoidal: Monoidal.FunctionIsMonoidal.type = Monoidal.FunctionIsMonoidal
    override val SelfIsMonoidal: Monoidal.FunctionIsMonoidal.type   = Monoidal.FunctionIsMonoidal

    type Exp = Function

    def eval[A, B]: ((A => B, A)) => B = {
      (f, a) => f(a)
    }

    def curry[A, B, C](f: ((C, A)) => B): C => A => B = {
      c => a => f((c, a))
    }
  }

  /** `Function` is monoidal closed under lazy tuple products with function types as exponentials. */
  given FunctionIsLazyClosed: Function is Closed {
    override given ClosedMonoidal: Cartesian.FunctionIsLazyCartesian.type = Cartesian.FunctionIsLazyCartesian
    override val SelfIsMonoidal: Cartesian.FunctionIsLazyCartesian.type   = Cartesian.FunctionIsLazyCartesian

    type Exp = Function

    def eval[A, B]: LazyTuple2[A => B, A] => B = {
      p => p._1(p._2)
    }

    def curry[A, B, C](f: LazyTuple2[C, A] => B): C => A => B = {
      c => a => f(LazyTuple2(c, a))
    }
  }
}
