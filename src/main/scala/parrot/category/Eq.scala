package parrot
package category

/** Equality on data types.
  *
  * Represents the intended equality of values of a data type, where
  *   - = is a decidable equivalence relation that holds if and only if the values are considered equal.
  */
trait Eq extends Type {

  /** Returns `true` if *a* and *b* are equal. */
  def equal(a: Self, b: Self): Boolean

  extension (a: Self)
    /** Infix form of [[equal]]. */
    final def ===(b: Self): Boolean = {
      Eq.this.equal(a, b)
    }

  /** Laws that any `Eq` must satisfy.
    *
    * Equality is an equivalence relation.
    */
  object EqLaws {
    extension (p: Boolean)
      private def implies(q: Boolean): Boolean = {
        !p || q
      }

    /** *a* = *a*
      */
    def reflexivity(a: Self): Boolean = {
      a === a
    }

    /** If *a* = *b*, then *b* = *a* */
    def symmetry(a: Self, b: Self): Boolean = {
      (a === b) `implies` (b === a)
    }

    /** If *a* = *b* and *b* = *c*, then *a* = *c* */
    def transitivity(a: Self, b: Self, c: Self): Boolean = {
      (a === b && b === c) `implies` (a === c)
    }
  }
}

object Eq {

  /** Summons the `Eq` instance of `A`. */
  def apply[A: Eq]: A is Eq = summon

  /** Structural equality, for data types whose `==` compares constructor trees.
    *
    * @note Not a given: `CanEqual` only permits `==`, it does not make `==` a structural equality. On plain classes
    *   `==` is reference identity, and on `Double` it is not even reflexive (`NaN == NaN` is `false`), so each
    *   instance states that `==` is the intended structural equality of its type by calling `structural`.
    */
  def structural[A](using CanEqual[A, A]): A is Eq = {
    new Eq {
      type Self = A

      def equal(a: A, b: A): Boolean = {
        a == b
      }
    }
  }

  /** `Nothing` has no values, so its equality is never asked.
    *
    * @note Not a given: a given whose `Self` is `Nothing` is found for every `T is Eq`.
    */
  val NothingIsEq: Nothing is Eq = {
    new Eq {
      type Self = Nothing

      def equal(a: Nothing, b: Nothing): Boolean = {
        a
      }
    }
  }

  /** Structural equality on `Unit`. */
  given UnitIsEq: (Unit is Eq) = structural

  /** Structural equality on `Boolean`. */
  given BooleanIsEq: (Boolean is Eq) = structural

  /** Structural equality on `Char`. */
  given CharIsEq: (Char is Eq) = structural

  /** Structural equality on `Int`. */
  given IntIsEq: (Int is Eq) = structural

  /** Structural equality on `Long`. */
  given LongIsEq: (Long is Eq) = structural

  /** Structural equality on `String`. */
  given StringIsEq: (String is Eq) = structural

  /** Structural equality on `BigInt`. */
  given BigIntIsEq: (BigInt is Eq) = {
    given CanEqual[BigInt, BigInt] = CanEqual.derived
    structural
  }

  /** Equality on `Double` as `java.lang.Double.compare` defines it: `NaN` equals itself, `0.0` and `-0.0` differ. */
  given DoubleIsEq: (Double is Eq) {
    def equal(a: Double, b: Double): Boolean = {
      java.lang.Double.compare(a, b) == 0
    }
  }

  /** Componentwise equality on `Option[A]`. */
  given OptionIsEq: [A: Eq] => Option[A] is Eq {
    def equal(a: Option[A], b: Option[A]): Boolean = {
      (a, b) match {
        case (Some(x), Some(y)) => x === y
        case (None, None)       => true
        case _                  => false
      }
    }
  }

  /** Componentwise equality on `Either[A, B]`. */
  given EitherIsEq: [A: Eq, B: Eq] => Either[A, B] is Eq {
    def equal(a: Either[A, B], b: Either[A, B]): Boolean = {
      (a, b) match {
        case (Left(x), Left(y))   => x === y
        case (Right(x), Right(y)) => x === y
        case _                    => false
      }
    }
  }

  /** Componentwise equality on `Tuple2[A, B]`. */
  given Tuple2IsEq: [A: Eq, B: Eq] => ((A, B) is Eq) {
    def equal(a: (A, B), b: (A, B)): Boolean = {
      a._1 === b._1 && a._2 === b._2
    }
  }

  /** Elementwise equality on `Seq[A]`. */
  given SeqIsEq: [C[X] <: Seq[X], A: Eq] => C[A] is Eq {
    def equal(a: C[A], b: C[A]): Boolean = {
      a.corresponds(b)((x, y) => x === y)
    }
  }
}
