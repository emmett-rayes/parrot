package parrot
package category

import Category.Type

/** The writer transformer: computations of a monad *M* on 𝒮 that also produce output, combined with a monoid *W*.
  *
  * Represents a monad *T* on 𝒮, where
  *   - *T*[*A*] = *M*[*W* × *A*]: the effects of *M*, then an output and a result ([[WriterT.FunctorOf]])
  *   - *η*(*a*) = *η*′(*ε*,*a*): no output
  *   - *μ* runs the outer computation, then the inner one, and combines their outputs in order
  *
  * Over the identity, it is the writer monad, [[Writer]]. Over `Option`, *T*[*A*] = 1 + *W* × *A*: a computation that
  * fails has no output, unlike in the failure transformer over a writer ([[OptionT]]).
  */
open class WriterT(
  tracked val monoid: Monoid.In[Total.Products.type],
  tracked val monad: Monad.On[Total.type],
) extends Monad(WriterT.FunctorOf(monoid, monad)) {

  def unit[A: Type]: A -> monad.M[(monoid.M, A)] = {
    a => monad.unit[(monoid.M, A)]((monoid.unit(()), a))
  }

  def flatten[A: Type]: monad.M[(monoid.M, monad.M[(monoid.M, A)])] -> monad.M[(monoid.M, A)] = {
    monad.bind[(monoid.M, monad.M[(monoid.M, A)]), (monoid.M, A)] { (w, m) =>
      monad.map[(monoid.M, A), (monoid.M, A)]((w2, a) => (monoid.multiply((w, w2)), a))(m)
    }
  }
}

object WriterT {

  /** The endofunctor of the writer transformer: *M*[*W* × −], which maps the result and keeps the output. */
  final class FunctorOf(
    tracked val monoid: Monoid.In[Total.Products.type],
    tracked val monad: Monad.On[Total.type],
  ) extends Endofunctor(Total) {
    type Self[A] = monad.M[(monoid.M, A)]

    def objects[A: Type]: monad.M[(monoid.M, A)] is Type = {
      Type.TIsType
    }

    def map[A: Type, B: Type](f: A -> B): monad.M[(monoid.M, A)] -> monad.M[(monoid.M, B)] = {
      monad.map[(monoid.M, A), (monoid.M, B)]((w, a) => (w, f(a)))
    }
  }
}

/** The writer monad of a monoid *W* in 𝒮: computations that also produce output, combined with the monoid, the writer
  * transformer [[WriterT]] over the identity.
  *
  * Represents a monad *M* on 𝒮, where
  *   - *M*[*A*] = *W* × *A*: an output and a result
  *   - *η*(*a*) = (*ε*,*a*): no output
  *   - *μ*(*w*,(*w*′,*a*)) = (*w* · *w*′,*a*): outputs are combined in order
  *
  * If *W* is commutative, the order of effects does not matter, and the Kleisli arrows form a monoidal category; if *W*
  * is also idempotent (a [[Semilattice]]), running an arrow twice is the same as running it once.
  */
open class Writer(tracked override val monoid: Monoid.In[Total.Products.type])
    extends WriterT(monoid, Monad.Identity)
