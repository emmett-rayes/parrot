package parrot
package category

import scala.quoted.*

/** The name of the type `T` as written in source, such as `List[Int]`: law checks are named after what they check.
  *
  * A type constructor is named without its parameters (`Tuple2`), the singleton type of an object or of a value that
  * refers to one by the name of the object (`Product`), and that of any other value by its path from an object
  * (`Product.op`).
  */
final class TypeName[T <: AnyKind](val name: String) extends caps.Pure

object TypeName {

  /** The name of `T`, computed at compile time where `T` is known: at the declaration of a test class. */
  inline given derived: [T <: AnyKind] => TypeName[T] = ${ derivedImpl[T] }

  private def derivedImpl[T <: AnyKind: Type](using Quotes): Expr[TypeName[T]] = {
    import quotes.reflect.*
    def isObject(ref: TermRef): Boolean = {
      ref.termSymbol.flags.is(Flags.Module)
    }
    def named(tpe: TypeRepr): TypeRepr = {
      tpe.dealias match {
        case ref: TermRef if !isObject(ref) =>
          ref.widenTermRefByName.dealias match {
            case widened: TermRef => named(widened)
            case _                => ref
          }
        case TypeLambda(_, _, AppliedType(constructor, _)) => constructor
        case other                                         => other
      }
    }
    def show(tpe: TypeRepr): String = {
      tpe match {
        case AppliedType(constructor, args) if defn.isTupleClass(constructor.typeSymbol) =>
          args.map(show).mkString("(", ", ", ")")
        case AppliedType(constructor, args) => s"${show(constructor)}[${args.map(show).mkString(", ")}]"
        case ref: TermRef if !isObject(ref) => s"${show(ref.qualifier)}.${ref.name}"
        case other                          => other.show(using Printer.TypeReprShortCode)
      }
    }
    '{ TypeName[T](${ Expr(show(named(TypeRepr.of[T]))) }) }
  }
}
