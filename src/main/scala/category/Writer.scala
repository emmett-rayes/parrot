package parrot
package category

/** The writer monad of a monoid *W* in 𝒮: computations that also produce output, combined with the monoid.
  *
  * Represents a monad *M* on 𝒮, where
  *   - *M*[*A*] = *W* × *A*: an output and a result ([[Writer.FunctorOf]])
  *   - *η*(*a*) = (*ε*,*a*): no output
  *   - *μ*(*w*,(*w*′,*a*)) = (*w* · *w*′,*a*): outputs are combined in order
  *
  * If *W* is commutative, the order of effects does not matter, and the Kleisli arrows form a monoidal category; if *W*
  * is also idempotent (a [[Semilattice]]), running an arrow twice is the same as running it once.
  */
open class Writer(tracked val W: Monoid { val V: Total.Product.type }) extends Monad(Writer.FunctorOf(W)) {

  def unit[A: Type]: A -> (W.M, A) = {
    a => (W.unit(()), a)
  }

  def flatten[A: Type]: ((W.M, (W.M, A))) -> (W.M, A) = {
    case (w, (w2, a)) => (W.multiply((w, w2)), a)
  }
}

object Writer {

  /** The endofunctor of a writer: *W* × −, which maps the result and keeps the output. */
  final class FunctorOf(tracked val W: Monoid { val V: Total.Product.type }) extends Endofunctor(Total) {
    type Self[A] = (W.M, A)

    def objects[A: Type]: (W.M, A) is Type = {
      Type.TIsType
    }

    def map[A: Type, B: Type](f: A -> B): ((W.M, A)) -> (W.M, B) = {
      (w, a) => (w, f(a))
    }
  }
}
