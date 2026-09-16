package parrot

import scala.util.{Failure, Success}

/** An Elgot monad over **Type**.
  *
  * Represents a monad *M* equipped with an iteration operator with respect to the coproduct + on **Type**, where
  *   - _†: (*A* → *M*[*B* + *A*]) → (*A* → *M*[*B*]) is the Elgot iteration operation.
  */
trait ElgotMonad extends Monad {
  type Self[_]
  type M = Self

  /** Maps a step morphism *f*: *A* → *M*[*B* + *A*] and an initial state *a* in *A* to an iterated computation in
    * *M*[*B*].
    *
    * Fixpoint Property:
    *   - *f*†(*a*) = *μ*(*M*([*η*,*f*†])(*f*(*a*)))
    *     - `iterate(f)(a) == f(a).flatMap { case Left(b) => unit(b); case Right(a) => iterate(f)(a) }`
    *
    * Naturality:
    *   - *M*(*g*)(*f*†(*a*)) = (*M*(*g* + *id*) ∘ *f*)†(*a*)
    *     - `iterate(f)(a).map(g) == iterate(a => f(a).map(_.left.map(g)))(a)`
    *
    * Dinaturality (Composition Identity):
    *   - ((*id* + *g*) ∘ *f*)†(*a*) = *μ*(*M*([*η*,((*id* + *f*) ∘ *g*)†])(*f*(*a*)))
    *     - `iterate(a => f(a).map(_.map(g)))(a) == f(a).flatMap { case Left(b) => unit(b); case Right(c) => iterate(c => f(g(c)))(c) }`
    *
    * Codiagonal (Double dagger):
    *   - (*f*†)† = ((*id* + ∇) ∘ *f*)†
    *     - `iterate(iterate(f))(a) == iterate(a => f(a).map(_.map(_.merge)))(a)`
    *
    * Uniformity (Simulation):
    *   - If *M*(*id* + *h*)(*f*(*a*)) = *g*(*h*(*a*)), then *f*†(*a*) = *g*†(*h*(*a*))
    *     - `f(a).map(_.map(h)) == g(h(a)) ==> (iterate(f)(a) == iterate(g)(h(a)))`
    *
    * Here *η* and *μ* are the unit and the multiplication of *M*, and
    *   - [*f*,*g*]: *A* + *B* → *C* is copairing / case analysis
    *   - ∇: *A* + *A* → *A* is the codiagonal morphism `[id,id]`
    *   - ι₁: *A* → *A* + *B* and ι₂: *B* → *A* + *B* are canonical coproduct injections (`Left` and `Right`)
    *
    * @note Having a default implementation does not mean that all Monads are ElgotMonads, since not all monads satisfy
    *   the laws automatically.
    */
  def iterate[A, B](f: A => M[Either[B, A]])(a: A): M[B] = {
    f(a).flatMap {
      case Left(b)  => unit(b)
      case Right(a) => iterate(f)(a)
    }
  }
}
