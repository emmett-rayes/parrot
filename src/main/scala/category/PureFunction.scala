package parrot
package category

opaque type PureFunction[A, B] >: (A -> B) <: (A -> B) = A -> B

object PureFunction {

  /** `Profunctor` instance for `PureFunction` on the category **Type**. */
  given PureFunctionIsProfunctor: PureFunction is Profunctor {
    type On = PureFunction

    override given ProfunctorOnPromonad: PureFunctionIsPromonad.type = PureFunctionIsPromonad
    override val OnIsPromonad: PureFunctionIsPromonad.type           = PureFunctionIsPromonad

    def dimap[A, B, C, D](f: C -> A, g: B -> D)(p: A -> B): C -> D = {
      f andThen p andThen g
    }
  }

  /** `Promonad` instance for `PureFunction` on the category **Type**. */
  given PureFunctionIsPromonad: PureFunction is Promonad {
    type On = PureFunction

    override given ProfunctorOnPromonad: PureFunctionIsPromonad.type = PureFunctionIsPromonad
    override val OnIsPromonad: PureFunctionIsPromonad.type           = PureFunctionIsPromonad

    def unit[A, B](f: A -> B): A -> B = {
      f
    }

    def multiply[A, B, C](q: B -> C, p: A -> B): A -> C = {
      a => q(p(a))
    }

    override def identity[A]: A -> A = {
      scala.Predef.identity
    }
  }

  /** `Cartesian` instance for `PureFunction` on the category **Type**. */
  given PureFunctionIsCartesian: PureFunction is Cartesian {
    type I      = Unit
    type Tensor = Tuple2

    override given CartesianPromonad: PureFunctionIsPromonad.type = PureFunctionIsPromonad
    override val SelfIsPromonad: PureFunctionIsPromonad.type      = PureFunctionIsPromonad

    def augment[A]: A -> Unit = {
      _ => ()
    }

    def first[A, B]: ((A, B)) -> A = {
      (a, _) => a
    }

    def second[A, B]: ((A, B)) -> B = {
      (_, b) => b
    }

    def product[C, A, B](f: C -> A, g: C -> B): C -> (A, B) = {
      c => (f(c), g(c))
    }
  }

  /** `Cartesian` instance for `PureFunction` on the category **Type** with lazy products. */
  given PureFunctionIsLazyCartesian: PureFunction is Cartesian {
    type I      = Unit
    type Tensor = LazyTuple2

    override given CartesianPromonad: PureFunctionIsPromonad.type = PureFunctionIsPromonad
    override val SelfIsPromonad: PureFunctionIsPromonad.type      = PureFunctionIsPromonad

    def augment[A]: A -> Unit = {
      _ => ()
    }

    def first[A, B]: LazyTuple2[A, B] -> A = {
      p => p._1
    }

    def second[A, B]: LazyTuple2[A, B] -> B = {
      p => p._2
    }

    def product[C, A, B](f: C -> A, g: C -> B): C -> LazyTuple2[A, B] = {
      c => LazyTuple2(f(c), g(c))
    }
  }

  /** `Cocartesian` instance for `PureFunction` on the category **Type**. */
  given PureFunctionIsCocartesian: PureFunction is Cocartesian {
    type Z      = Nothing
    type Tensor = Either

    override given CocartesianPromonad: PureFunctionIsPromonad.type = PureFunctionIsPromonad
    override val SelfIsPromonad: PureFunctionIsPromonad.type        = PureFunctionIsPromonad

    def absurd[A]: Nothing -> A = {
      n => n
    }

    def left[A, B]: A -> Either[A, B] = {
      Left(_)
    }

    def right[A, B]: B -> Either[A, B] = {
      Right(_)
    }

    def sum[A, B, C](f: A -> C, g: B -> C): Either[A, B] -> C = {
      _.fold(f, g)
    }
  }

  /** `PureFunction` is a trivial `Restriction` on the category **Type**, where every morphism is total. */
  given PureFunctionIsRestriction: PureFunction is Restriction {
    override given RestrictionPromonad: PureFunctionIsPromonad.type = PureFunctionIsPromonad
    override val SelfIsPromonad: PureFunctionIsPromonad.type        = PureFunctionIsPromonad

    def restrict[A, B](p: A -> B): A -> A = {
      scala.Predef.identity
    }
  }
}
