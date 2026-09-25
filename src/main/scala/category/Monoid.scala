package parrot
package category

import scala.annotation.targetName
import scala.util.{Failure, Try}

/** A monoid object on an underlying monoidal category **C**.
  *
  * Represents a monoid object (*M*, *μ*, *η*) in (**C**, ⊗, *I*), where
  *   - *η*: *I* ~> *M* is the unit morphism
  *   - *μ*: *M* ⊗ *M* ~> *M* is the multiplication morphism
  */
trait Monoid {
  type Self
  final type M = Self

  type In[_, _]: {Promonad, Monoidal}

  val Prom: In is Promonad = summon
  import Prom.*

  val Mon: In is Monoidal = summon
  import Mon.*

  /** The unit morphism *η*: *I* ~> *M*. */
  def unit: I ~> M

  /** The multiplication morphism *μ*: *M* ⊗ *M* ~> *M*. */
  def multiply: (M * M) ~> M

  /** Laws that any `Monoid` must satisfy. */
  object MonoidLaws {

    /** *μ* ∘ (*η* ⊗ *id*_M) = *λ*_M
      */
    def leftIdentity(using (I * M) ~> M is Eq): Boolean = {
      ((unit *** identity[M]) >>> multiply) === leftUnitor[M]
    }

    /** *μ* ∘ (*id*_M ⊗ *η*) = *ρ*_M
      */
    def rightIdentity(using (M * I) ~> M is Eq): Boolean = {
      ((identity[M] *** unit) >>> multiply) === rightUnitor[M]
    }

    /** *μ* ∘ (*μ* ⊗ *id*_M) = *μ* ∘ (*id*_M ⊗ *μ*) ∘ *α*_{M,M,M}
      */
    def associativity(using ((M * M) * M) ~> M is Eq): Boolean = {
      ((multiply *** identity[M]) >>> multiply) === (associate[M, M, M] >>> (identity[M] *** multiply) >>> multiply)
    }
  }
}

object Monoid {

  /** Refines the `In` type of `Monoid` to `T`. */
  infix type in[M <: Monoid, T[_, _]] = Monoid { type In = T }

  /** Summons the `Monoid` instance of `M`. */
  def apply[M: Monoid]: M is Monoid = summon

  /** An additive monoid (*M*, +, 0) internal to (**Type**, ×, Unit). */
  trait Additive extends Monoid {
    type Self

    type In = Function

    override val Mon: Function is Monoidal.`with`[Unit, [A, B] =>> (A, B)] = summon

    import Mon.*
    import Prom.*

    /** The unit element 0 of *M*. */
    def zero: M

    /** Combines two elements in *M*. */
    def plus(x: M, y: M): M

    override def unit: I ~> M = {
      _ => zero
    }

    override def multiply: (M * M) ~> M = {
      case (x, y) => plus(x, y)
    }

    extension (x: M)
      /** Infix extension for [[plus]]. */
      @targetName("plusExt")
      def plus(y: M): M = {
        Additive.this.plus(x, y)
      }

    extension (x: M)
      /** Alias for [[plus]]. */
      def +(y: M): M = {
        x.plus(y)
      }
  }

  object Additive {

    /** Summons the `Additive` instance of `M`. */
    def apply[M: Additive]: M is Additive = summon

    /** `Option[A]` is a `Monoid.Additive` under `orElse` with `None` as zero. */
    given OptionIsAdditive: [A] => Option[A] is Additive {
      def zero: Option[A] = {
        None
      }

      def plus(x: Option[A], y: Option[A]): Option[A] = {
        x.orElse(y)
      }
    }

    /** `Try[A]` is a `Monoid.Additive` under `orElse` with `Failure` as zero. */
    given TryIsAdditive: [A] => Try[A] is Additive {
      def zero: Try[A] = {
        Failure(Exception())
      }

      def plus(x: Try[A], y: Try[A]): Try[A] = {
        x.orElse(y)
      }
    }

    /** `A => B` is a `Monoid.Additive` if `B` is a `Monoid.Additive`. */
    given FunctionIsAdditive: [A, B: Additive] => Function[A, B] is Additive {
      def zero: A => B = {
        _ => Additive[B].zero
      }

      def plus(f: A => B, g: A => B): A => B = {
        a => f(a) + g(a)
      }
    }
  }

  /** A multiplicative monoid (*M*, *, 1) internal to (**Type**, ×, Unit). */
  trait Multiplicative extends Monoid {
    type Self

    type In = Function

    override val Mon: Function is Monoidal.`with`[Unit, [A, B] =>> (A, B)] = summon

    import Mon.*
    import Prom.*

    /** The unit element 1 of *M*. */
    def one: M

    /** Combines two elements in *M*. */
    def times(x: M, y: M): M

    override def unit: I ~> M = {
      _ => one
    }

    override def multiply: (M * M) ~> M = {
      case (x, y) => times(x, y)
    }

    extension (x: M)
      /** Infix extension for [[times]]. */
      @targetName("timesExt")
      def times(y: M): M = {
        Multiplicative.this.times(x, y)
      }

    extension (x: M)
      /** Alias for [[times]]. */
      def *(y: M): M = {
        x.times(y)
      }
  }

  object Multiplicative {

    /** Summons the `Multiplicative` instance of `M`. */
    def apply[M: Multiplicative]: M is Multiplicative = summon

    /** `Int` is a `Monoid.Multiplicative` under multiplication with `1` as one. */
    given IntIsMultiplicative: Int is Multiplicative {
      def one: Int = {
        1
      }

      def times(x: Int, y: Int): Int = {
        x * y
      }
    }

    /** `A => B` is a `Monoid.Multiplicative` if `B` is a `Monoid.Multiplicative`. */
    given FunctionIsMultiplicative: [A, B: Multiplicative] => Function[A, B] is Multiplicative {
      def one: A => B = {
        _ => Multiplicative[B].one
      }

      def times(f: A => B, g: A => B): A => B = {
        a => f(a) * g(a)
      }
    }
  }
}
