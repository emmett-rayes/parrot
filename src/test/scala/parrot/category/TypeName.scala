package parrot
package category

import scala.quoted.*

/** The name of the type `T` as written in source, such as `List[Int]`: law checks are named after what they check.
  *
  * A type constructor is named without its parameters (`Tuple2`), and the singleton type of an object or of a value
  * that refers to one by the name of the object (`Product`).
  */
final class TypeName[T <: AnyKind](val name: String) extends caps.Pure

object TypeName {

  /** The name of `T`, computed at compile time where `T` is known: at the declaration of a test class. */
  inline given derived: [T <: AnyKind] => TypeName[T] = ${ derivedImpl[T] }

  private def derivedImpl[T <: AnyKind: Type](using Quotes): Expr[TypeName[T]] = {
    import quotes.reflect.*
    def named(tpe: TypeRepr): TypeRepr = {
      tpe.dealias match {
        case ref: TermRef if !ref.termSymbol.flags.is(Flags.Module) => named(ref.widenTermRefByName)
        case TypeLambda(_, _, AppliedType(constructor, _))           => constructor
        case other                                                   => other
      }
    }
    def show(tpe: TypeRepr): String = {
      tpe match {
        case AppliedType(constructor, args) if defn.isTupleClass(constructor.typeSymbol) =>
          args.map(show).mkString("(", ", ", ")")
        case AppliedType(constructor, args) => s"${show(constructor)}[${args.map(show).mkString(", ")}]"
        case other                          => other.show(using Printer.TypeReprShortCode)
      }
    }
    '{ TypeName[T](${ Expr(show(named(TypeRepr.of[T]))) }) }
  }
}
