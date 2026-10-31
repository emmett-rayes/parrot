package parrot
package category

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
  tracked val W: Monoid { val V: Total.Product.type },
  tracked val M: Monad.On[Total.type],
) extends Monad(WriterT.FunctorOf(W, M)) {

  def unit[A: Type]: A -> M.M[(W.M, A)] = {
    a => M.unit[(W.M, A)]((W.unit(()), a))
  }

  def flatten[A: Type]: M.M[(W.M, M.M[(W.M, A)])] -> M.M[(W.M, A)] = {
    M.bind[(W.M, M.M[(W.M, A)]), (W.M, A)] { (w, m) =>
      M.map[(W.M, A), (W.M, A)]((w2, a) => (W.multiply((w, w2)), a))(m)
    }
  }
}

object WriterT {

  /** The endofunctor of the writer transformer: *M*[*W* × −], which maps the result and keeps the output. */
  final class FunctorOf(
    tracked val W: Monoid { val V: Total.Product.type },
    tracked val M: Monad.On[Total.type],
  ) extends Endofunctor(Total) {
    type Self[A] = M.M[(W.M, A)]

    def objects[A: Type]: M.M[(W.M, A)] is Type = {
      Type.TIsType
    }

    def map[A: Type, B: Type](f: A -> B): M.M[(W.M, A)] -> M.M[(W.M, B)] = {
      M.map[(W.M, A), (W.M, B)]((w, a) => (w, f(a)))
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
open class Writer(tracked override val W: Monoid { val V: Total.Product.type }) extends WriterT(W, Monad.Identity)
