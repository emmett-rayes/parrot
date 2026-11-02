package parrot
package category

import Category.Type

/** The failure transformer: computations of a monad *M* on 𝒮 that may also fail.
  *
  * Represents a monad *T* on 𝒮, where
  *   - *T*[*A*] = *M*[1 + *A*]: the effects of *M*, then a result or none ([[OptionT.FunctorOf]])
  *   - *η*(*a*) = *η*′(*Some*(*a*))
  *   - *μ* runs the inner computation of a result and keeps a failure, with the effects of *M* in both cases
  *
  * Over the identity, it is `Option` ([[Monad.OptionIsMonad]]). Over a writer, *T*[*A*] = *W* × (1 + *A*): the output
  * is produced whether or not the computation fails. This is the shape of a parser that reports what it expected on
  * success and on failure.
  */
open class OptionT(tracked val monad: Monad.On[Total.type]) extends Monad(OptionT.FunctorOf(monad)) {

  def unit[A: Type]: A -> monad.M[Option[A]] = {
    a => monad.unit[Option[A]](Some(a))
  }

  def flatten[A: Type]: monad.M[Option[monad.M[Option[A]]]] -> monad.M[Option[A]] = {
    monad.bind[Option[monad.M[Option[A]]], Option[A]] {
      case Some(m) => m
      case None    => monad.unit[Option[A]](None)
    }
  }
}

object OptionT {

  /** The endofunctor of the failure transformer: *M*[1 + −], which maps a result and keeps a failure. */
  final class FunctorOf(tracked val monad: Monad.On[Total.type]) extends Endofunctor(Total) {
    type Self[A] = monad.M[Option[A]]

    def objects[A: Type]: monad.M[Option[A]] is Type = {
      Type.TIsType
    }

    def map[A: Type, B: Type](f: A -> B): monad.M[Option[A]] -> monad.M[Option[B]] = {
      monad.map[Option[A], Option[B]](_.map(f))
    }
  }

  /** The classical structure of the failure transformer, where
    *   - 0 = *η*′(*None*), *m̄* and *m̄*ᶜ keep the effects of *m* and forget or invert its result
    *   - *m* ⊳ *n* keeps the effects of *m*, and where *m* fails adds those of *n*
    *
    * For a writer whose monoid is a [[Semilattice]], **R1**, **R3** and **R4** hold. **R2** does not, for any writer
    * with a non-trivial output: a failing test stops the effects after it, so *m̄* ⨾ *n̄* and *n̄* ⨾ *m̄* produce
    * different outputs where one of them fails. The laws of zero and complement fail as well, since 0 has no effects
    * while *m* ⨾ 0 and *m̄* ⨾ *m̄*ᶜ have those of *m*. Silent tests, which drop the effects of *m*, keep these laws
    * exact instead, at the cost of **R1** and **R4**.
    */
  open class ClassicalOf(tracked val transformer: OptionT) extends Monad.Classical(transformer) {
    import transformer.monad.M

    def restrict[A](m: M[Option[A]]): M[Option[Unit]] = {
      transformer.monad.map[Option[A], Option[Unit]](_.map(_ => ()))(m)
    }

    def zero[A]: M[Option[A]] = {
      transformer.monad.unit[Option[A]](None)
    }

    def complement[A](m: M[Option[A]]): M[Option[Unit]] = {
      transformer.monad.map[Option[A], Option[Unit]](r => if r.isEmpty then Some(()) else None)(m)
    }

    def orElse[A](m: M[Option[A]], n: -> M[Option[A]]): M[Option[A]] = {
      transformer.monad.bind[Option[A], Option[A]] {
        case None   => n
        case result => transformer.monad.unit[Option[A]](result)
      }(m)
    }

    override def attempt[A](m: M[Option[A]]): M[Option[Option[A]]] = {
      transformer.monad.map[Option[A], Option[Option[A]]](r => Some(r))(m)
    }
  }
}
