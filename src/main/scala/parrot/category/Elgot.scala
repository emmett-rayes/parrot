package parrot
package category

/** An iteration structure on a bistrong promonad *P* over a cocartesian category **M**.
  *
  * Represents an Elgot operator (Elgot; Bloom–Ésik), a uniform Conway iteration operator, where
  *   - † is the iteration operator
  *
  * It is a [[GuardedIteration]] in which every step is guarded, and its laws are the laws of [[GuardedIteration]],
  * without their premise. Elgot operators are equivalent to traces for coproducts. See [[Traced.OfElgot]]. Elgot
  * operators are dual to Conway fixed points. See [[Conway]].
  */
abstract class Elgot(tracked override val strong: StrongPromonad { val monoidal: Cocartesian })
    extends GuardedIteration(strong)

object Elgot {

  /** The iteration structures on a bistrong promonad with the strength *S*. */
  type On[S <: Bistrong] = Elgot { val strong: S }

  /** The iteration on *P*ᵒᵖ of a Conway operator *C* on *P*: fixed points read backwards. */
  open class OfConway(tracked val conway: Conway)
      extends Elgot(Bistrong.Op(conway.strong)) {
    import strong.{monoidal, profunctor}
    import monoidal.+
    import profunctor.P
    import profunctor.arrows.-->
    import profunctor.category.Obj

    def iterate[A: Obj, X: Obj](p: X --> (A + X)): (X --> A) = {
      conway.fix[A, X](p)
    }
  }

  /** The iteration of a trace *T* on coproducts: *p*† = *tr*(*p* ∘ *η*(∇)). */
  open class OfTraced(
    tracked val traced: Traced.On[Freyd.On[StrongPromonad { val monoidal: Cocartesian }]],
  ) extends Elgot(traced.premonoidal.strong) {
    import strong.{monoidal, profunctor}
    import monoidal.+
    import profunctor.{P, >>>}
    import profunctor.arrows.-->
    import profunctor.category.Obj

    private given TensorIsObj: [A: Obj, B: Obj] => ((A + B) is Obj) = monoidal.tensor.objects[A, B]

    def iterate[A: Obj, X: Obj](p: X --> (A + X)): (X --> A) = {
      traced.trace[X, A, X](profunctor.unit(monoidal.codiagonal[X]) >>> p)
    }
  }
}
