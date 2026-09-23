package parrot
package legacy

import scala.compiletime.asMatchable
import scala.language.implicitConversions

/** An isomorphism-aware function type that normalizes unit and product inputs.
  *
  * Reduction rules:
  *   - `(Unit, Unit) ==> Out`  reduces to  `Unit => Out`
  *   - `(Unit, B)    ==> Out`  reduces to  `B => Out`
  *   - `(A, Unit)    ==> Out`  reduces to  `A => Out`
  *   - `(A, B)       ==> Out`  reduces to  `(A, B) => Out` (JVM `Function2`)
  *   - `A            ==> Out`  reduces to  `A => Out`
  */
type IsoFunction[In, Out] = In match {
  case (Unit, Unit) => Unit => Out
  case (Unit, b)    => b => Out
  case (a, Unit)    => a => Out
  case (a, b)       => (a, b) => Out
  case _            => In => Out
}

infix type ==>[A, B] = IsoFunction[A, B]

object IsoFunction {

  /** A reusable singleton implementing both arities with zero heap allocations. */
  object UniversalId extends Function1[Any, Any] with Function2[Any, Any, Any] {
    def apply(a: Any): Any = a
    def apply(a: Any, b: Any): Any = (a, b)
  }

  /** The canonical identity arrow for `==>`. */
  def id[A]: A ==> A = UniversalId.asInstanceOf[A ==> A]

  /** Invokes an `IsoFunction` on its input argument without unchecked casts. */
  def invoke[In, Out](f: In ==> Out, in: In): Out = {
    f match {
      case f2: Function2[?, ?, ?] =>
        val p = in.asInstanceOf[(Any, Any)]
        f2.asInstanceOf[(Any, Any) => Out](p._1, p._2)
      case f1: Function1[?, ?] =>
        val fn = f1.asInstanceOf[Any => Out]
        in.asMatchable match {
          case ((), b) => fn(b)
          case (a, ()) => fn(a)
          case _       => fn(in)
        }
    }
  }

  /** Constructs an arrow that can be invoked as Function1 or Function2. */
  def arrow[In, Out](f1: In => Out, f2: (Any, Any) => Out): In ==> Out = {
    val res: Any = new Function1[In, Out] with Function2[Any, Any, Out] {
      def apply(in: In): Out = f1(in)
      def apply(a: Any, b: Any): Out = f2(a, b)
    }
    res.asInstanceOf[In ==> Out]
  }

  given fn1ToIso: [A, B] => Conversion[A => B, A ==> B] = f => {
    val res: Any = (a: Any) => f(a.asInstanceOf[A])
    res.asInstanceOf[A ==> B]
  }

  given fn2ToIso: [A, B, Out] => Conversion[(A, B) => Out, (A, B) ==> Out] = f2 => {
    val res: Any = f2
    res.asInstanceOf[(A, B) ==> Out]
  }

  extension [In, Out](f: In ==> Out) {
    def applySingle(in: In): Out = invoke(f, in)
  }
}
