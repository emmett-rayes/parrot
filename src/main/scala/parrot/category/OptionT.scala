package parrot
package category

/** The failure transformer: computations of a monad *M* on 𝒮 that may also fail.
  *
  * Represents a monad *T* on 𝒮, where
  *   - *T*[*A*] = *M*[1 + *A*]: the effects of *M*, then a result or none ([[OptionT.FunctorOf]])
  *   - *η*(*a*) = *η*′(`Some`(*a*))
  *   - *μ* runs the inner computation of a result and keeps a failure, with the effects of *M* in both cases
  *
  * Over a writer, *T*[*A*] = *W* × (1 + *A*): the output is produced whether or not the computation fails. This is the
  * shape of a parser that reports what it expected on success and on failure.
  */
open class OptionT(tracked val M: Monad.On[Total.type]) extends Monad(OptionT.FunctorOf(M)) {

  def unit[A: Type]: A -> M.M[Option[A]] = {
    a => M.unit[Option[A]](Some(a))
  }

  def flatten[A: Type]: M.M[Option[M.M[Option[A]]]] -> M.M[Option[A]] = {
    M.bind[Option[M.M[Option[A]]], Option[A]] {
      case Some(m) => m
      case None    => M.unit[Option[A]](None)
    }
  }
}

object OptionT {

  /** The endofunctor of the failure transformer: *M*[1 + −], which maps a result and keeps a failure. */
  final class FunctorOf(tracked val M: Monad.On[Total.type]) extends Endofunctor(Total) {
    type Self[A] = M.M[Option[A]]

    def objects[A: Type]: M.M[Option[A]] is Type = {
      Type.TIsType
    }

    def map[A: Type, B: Type](f: A -> B): M.M[Option[A]] -> M.M[Option[B]] = {
      M.map[Option[A], Option[B]](_.map(f))
    }
  }

  /** The classical structure of the failure transformer, where
    *   - 0 = *η*′(`None`), *m̄* and *m̄*ᶜ keep the effects of *m* and forget or invert its result
    *   - *m* ⊳ *n* keeps the effects of *m*, and where *m* fails adds those of *n*
    *
    * For a writer whose monoid is a [[Semilattice]], **R1**, **R3** and **R4** hold. **R2** does not, for any writer
    * with a non-trivial output: a failing test stops the effects after it, so *m̄* ⨾ *n̄* and *n̄* ⨾ *m̄* produce
    * different outputs where one of them fails. The laws of zero and complement fail as well, since 0 has no effects
    * while *m* ⨾ 0 and *m̄* ⨾ *m̄*ᶜ have those of *m*. Silent tests, which drop the effects of *m*, keep these laws
    * exact instead, at the cost of **R1** and **R4**.
    */
  open class ClassicalOf(tracked val T: OptionT) extends ClassicalMonad(T) {

    def restrict[A](m: T.M.M[Option[A]]): T.M.M[Option[Unit]] = {
      T.M.map[Option[A], Option[Unit]](_.map(_ => ()))(m)
    }

    def zero[A]: T.M.M[Option[A]] = {
      T.M.unit[Option[A]](None)
    }

    def complement[A](m: T.M.M[Option[A]]): T.M.M[Option[Unit]] = {
      T.M.map[Option[A], Option[Unit]](r => if r.isEmpty then Some(()) else None)(m)
    }

    def orElse[A](m: T.M.M[Option[A]], n: -> T.M.M[Option[A]]): T.M.M[Option[A]] = {
      T.M.bind[Option[A], Option[A]] {
        case None   => n
        case result => T.M.unit[Option[A]](result)
      }(m)
    }

    override def attempt[A](m: T.M.M[Option[A]]): T.M.M[Option[Option[A]]] = {
      T.M.map[Option[A], Option[Option[A]]](r => Some(r))(m)
    }
  }
}
