package parrot
package category

import java.util.Objects
import scala.compiletime.asMatchable

/** A lazy 2-tuple whose elements are evaluated on demand.
  *
  * Extends [[scala.Product2]] for product decomposition and interop.
  */
trait LazyTuple2[+A, +B] extends Product2[A, B] {
  override def productArity: Int = 2

  override def productElement(n: Int): Any = n match {
    case 0 => _1
    case 1 => _2
    case _ => throw new IndexOutOfBoundsException(s"$n is out of bounds for LazyTuple2 (expected 0 or 1)")
  }

  override def canEqual(that: Any): Boolean = that.asMatchable match {
    case _: LazyTuple2[?, ?] => true
    case _                   => false
  }

  override def equals(that: Any): Boolean = that.asMatchable match {
    case other: LazyTuple2[?, ?] =>
      Objects.equals(this._1, other._1) && Objects.equals(this._2, other._2)
    case _ => false
  }

  override def hashCode(): Int = {
    Objects.hash(_1.asInstanceOf[AnyRef], _2.asInstanceOf[AnyRef])
  }

  override def toString: String = s"LazyTuple2(${_1}, ${_2})"
}

object LazyTuple2 {

  /** Constructs a [[LazyTuple2]] with by-name arguments evaluated on demand. */
  def apply[A, B](a: => A, b: => B): LazyTuple2[A, B] = new LazyTuple2[A, B] {
    lazy val _1: A = a
    lazy val _2: B = b
  }

  /** Extractor for pattern matching on [[LazyTuple2]]. */
  def unapply[A, B](p: LazyTuple2[A, B]): LazyTuple2[A, B] = p

  given canEqualLazyTuple2: [A, B] => (CanEqual[A, A], CanEqual[B, B]) => CanEqual[LazyTuple2[A, B], LazyTuple2[A, B]] =
    CanEqual.derived
}
