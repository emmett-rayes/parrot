package parrot
package category

/** The category 𝒮 of total, pure Scala programs.
  *
  * Represents 𝒮, where
  *   - the objects are all types
  *   - 𝒮(*A*,*B*) are the total, pure functions *A* → *B*
  *   - *id* = *a* ↦ *a*
  *   - *g* ∘ *f* = *a* ↦ *g*(*f*(*a*))
  *
  * 𝒮 is bicartesian closed. See [[Product]], [[Coproduct]], [[Exponential]].
  *
  * @note Capture checking makes functions pure. Totality is promised by the user. A function that may diverge belongs
  *   to 𝒫 instead. See [[Partial]].
  */
object Total extends Category {
  type Self[A, B] = A -> B
  type Obj        = Type

  def identity[A: Type]: A -> A = {
    a => a
  }

  def compose[A: Type, B: Type, C: Type](g: B -> C, f: A -> B): A -> C = {
    a => g(f(a))
  }

  /** 𝒮 as a promonad over itself. */
  object Functions extends Promonad.Hom(Total)

  /** Pairs as a bifunctor *A* × *B* on 𝒮. */
  object Tuple2IsBifunctor extends Bifunctor(Total, Total, Total) {
    type Self = Tuple2

    def objects[A: Type, B: Type]: (A, B) is Type = {
      Type.TIsType
    }

    def bimap[A1: Type, B1: Type, A2: Type, B2: Type](f: A1 -> A2, g: B1 -> B2): ((A1, B1)) -> (A2, B2) = {
      (a, b) => (f(a), g(b))
    }
  }

  /** Tagged unions as a bifunctor *A* + *B* on 𝒮. */
  object EitherIsBifunctor extends Bifunctor(Total, Total, Total) {
    type Self = Either

    def objects[A: Type, B: Type]: Either[A, B] is Type = {
      Type.TIsType
    }

    def bimap[A1: Type, B1: Type, A2: Type, B2: Type](f: A1 -> A2, g: B1 -> B2): Either[A1, B1] -> Either[A2, B2] = {
      case Left(a)  => Left(f(a))
      case Right(b) => Right(g(b))
    }
  }

  /** The products of 𝒮: pairs, with the unit type 1 as terminal object. */
  object Product extends Cartesian(Total, Tuple2IsBifunctor) {
    type I = Unit

    def unitObject: Unit is Type = {
      Type.TIsType
    }

    def fst[A: Type, B: Type]: ((A, B)) -> A = {
      _._1
    }

    def snd[A: Type, B: Type]: ((A, B)) -> B = {
      _._2
    }

    def pair[X: Type, A: Type, B: Type](f: X -> A, g: X -> B): X -> (A, B) = {
      x => (f(x), g(x))
    }

    def discard[A: Type]: A -> Unit = {
      _ => ()
    }
  }

  /** The coproducts of 𝒮: tagged unions, with the empty type 0 as initial object. */
  object Coproduct extends Cocartesian(Total, EitherIsBifunctor) {
    type I = Nothing

    def unitObject: Nothing is Type = {
      Type.TIsType
    }

    def inl[A: Type, B: Type]: A -> Either[A, B] = {
      a => Left(a)
    }

    def inr[A: Type, B: Type]: B -> Either[A, B] = {
      b => Right(b)
    }

    def copair[A: Type, B: Type, X: Type](f: A -> X, g: B -> X): Either[A, B] -> X = {
      case Left(a)  => f(a)
      case Right(b) => g(b)
    }

    def absurd[A: Type]: Nothing -> A = {
      n => n
    }
  }

  /** The internal homs of 𝒮: function types, with evaluation and currying. */
  object Exponential extends Closed(Product) {
    type Exp[A, B] = A -> B

    def objects[A: Type, B: Type]: (A -> B) is Type = {
      Type.TIsType
    }

    def eval[A: Type, B: Type]: ((A -> B, A)) -> B = {
      (f, a) => f(a)
    }

    def curry[A: Type, B: Type, C: Type](f: ((C, A)) -> B): C -> A -> B = {
      c => a => f((c, a))
    }
  }
}
