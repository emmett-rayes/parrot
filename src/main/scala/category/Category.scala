package parrot
package category

import scala.annotation.targetName

/** A category with objects *Ob*(**Type**).
  *
  * Represents a category with morphisms *A* --> *B*, where
  *   - *id* is the identity morphism
  *   - ∘ is the composition
  */
trait Category {
  type Self[_, _]
  final type --> = Self

  /** The identity morphism *id*: *A* --> *A*. */
  def identity[A]: A --> A

  /** Composes two morphisms *p*: *B* --> *C* and *q*: *A* --> *B* to a morphism *p* ∘ *q*: *A* --> *C*. */
  def compose[A, B, C](p: B --> C, q: A --> B): A --> C

  /** Composes two morphisms *p*: *A* --> *B* and *q*: *B* --> *C* to a morphism *p* ⨾ *q*: *A* --> *C* in the
    * diagrammatic order.
    */
  def andThen[A, B, C](p: A --> B, q: B --> C): A --> C = {
    compose(q, p)
  }

  extension [B, C](p: B --> C)
    /** Infix extension for [[compose]]. */
    @targetName("composeExt")
    infix def compose[A](q: A --> B): A --> C = {
      Category.this.compose(p, q)
    }

  extension [A, B](p: A --> B)
    /** Infix extension for [[andThen]]. */
    @targetName("andThenExt")
    infix def andThen[C](q: B --> C): A --> C = {
      Category.this.andThen(p, q)
    }

  extension [B, C](p: B --> C)
    /** Alias for [[compose]]. */
    def <<<[A](q: A --> B): A --> C = {
      p compose q
    }

  extension [A, B](p: A --> B)
    /** Alias for [[andThen]]. */
    def >>>[C](q: B --> C): A --> C = {
      p andThen q
    }

  /** Laws that any `Category` must satisfy. */
  object CategoryLaws {

    /** *id* ∘ *f* = *f*
      */
    def leftIdentity[A, B](f: A --> B)(using (A --> B) is Eq): Boolean = {
      (f >>> identity[B]) === f
    }

    /** *f* ∘ *id* = *f*
      */
    def rightIdentity[A, B](f: A --> B)(using (A --> B) is Eq): Boolean = {
      (identity[A] >>> f) === f
    }

    /** *h* ∘ (*g* ∘ *f*) = (*h* ∘ *g*) ∘ *f*
      */
    def associativity[A, B, C, D](
      f: A --> B,
      g: B --> C,
      h: C --> D,
    )(using (A --> D) is Eq): Boolean = {
      ((f >>> g) >>> h) === (f >>> (g >>> h))
    }
  }
}

object Category {

  /** Summons the `Category` instance of `C`. */
  def apply[C[_, _]: Category]: C is Category = summon

  /** `Category` instance for `=:=` on the discrete category *Ob*(**Type**). */
  given TypeEqIsCategory: =:= is Category {
    def identity[A]: A =:= A = {
      summon[A =:= A]
    }

    def compose[A, B, C](p: B =:= C, q: A =:= B): A =:= C = {
      q.andThen(p)
    }
  }

  /** `Category` instance for `Function`. */
  given FunctionIsCategory: Function is Category {
    def identity[A]: A => A = {
      scala.Predef.identity
    }

    def compose[A, B, C](p: B => C, q: A => B): A => C = {
      a => p(q(a))
    }
  }
}
