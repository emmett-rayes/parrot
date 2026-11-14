package parrot
package benchmarks

/** The syntax tree of fastparse's documented JSON grammar, which all its ports build. */
object Js {
  sealed trait Val
  final case class Str(value: String)               extends Val
  final case class Obj(value: Seq[(String, Val)])   extends Val
  final case class Arr(value: Seq[Val])             extends Val
  final case class Num(value: Double)               extends Val
  case object False                                 extends Val
  case object True                                  extends Val
  case object Null                                  extends Val
}
