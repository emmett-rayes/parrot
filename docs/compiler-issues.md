# Compiler issues to file

Scala compiler behaviors that cost time in this repository, with minimal reproductions ready to be filed upstream.
The design of the library is in [`DESIGN.md`](DESIGN.md).

All four have been verified with Scala 3.10.0. The first two are worked around by turning the flags (`-Wsafe-init`,
`-Wunused:imports`) off in `build.sbt` and `pants.toml`, the third by type patterns, the fourth by not exporting givens.

**`-Wsafe-init` false positive when a `tracked` constructor parameter is forwarded to a parent class.** Options:
`-source:future -language:experimental.modularity -Wsafe-init`.

```scala
abstract class Base(tracked val x: AnyRef)
abstract class Middle(tracked val y: AnyRef) extends Base(y)

class ViaClass extends Middle("a")   // warning: Access non-initialized value y
object ViaObject extends Middle("a") // no warning

abstract class PlainBase(val x: AnyRef)
abstract class PlainMiddle(val y: AnyRef) extends PlainBase(y)
class PlainClass extends PlainMiddle("a") // no warning

@main def run(): Unit = println((ViaClass().x, ViaObject.x, PlainClass().x))
```

The program prints `(a,a,a)`: `y` is initialized when it is used. The same chain instantiated by an `object`, or
written without `tracked`, produces no warning.

**`-Wunused:imports` reports a renamed type import as unused although it is used.** Options: `-Wunused:all`.

```scala
trait Box { type T }

class Uses(val b: Box) {
  import b.T as U // warning: unused import
  def f(u: U): U = u
}
```

Without the rename (`import b.T` and `T` in the signature) there is no warning. The same happens for type aliases and
abstract type members, with or without braces around the selector, and with or without other imports in scope.

**Capture checking mis-types patterns of case classes without fields.** New in Scala 3.10.0, and still in 3.10.1-RC1.
Options: `-language:experimental.captureChecking`.

```scala
sealed trait Fn[A, B]
final case class Id[A]() extends Fn[A, A]
final case class Fst[A, B]() extends Fn[(A, B), A]
final case class Snd[A, B]() extends Fn[(A, B), B]

def isId[A, B](f: Fn[A, B]): Boolean = f match {
  case Id() => true // error: Found: Id[A], Required: Boolean
  case _    => false
}

def both[A, B, C](f: Fn[A, B], g: Fn[A, C]): Boolean = (f, g) match {
  case (Fst(), Snd()) => true // crash: unexpected type of Fst.unapply(...).&&
  case _              => false
}
```

Scala 3.9.0 compiles both. The pattern matcher combines the `unapply` of a case class without fields with `&&`, as a
`Boolean`, but capture checking types it as returning the case class. A type pattern, `case _: Id[?]`, matches the same
values and refines the type arguments the same way; `Fn` and `StrictParser` use it.

**Capture checking rejects the export of a given whose type depends on a path.** Also in 3.10.1-RC1. Options:
`-language:experimental.captureChecking`.

```scala
trait Ev { type Self }

class Chosen(val U: Ev) {
  given IIsEv: (Ev { type Self = U.Self }) = U
}

class Mon(val U: Chosen) {
  export U.IIsEv // error: Found: Ev{type Self = Mon.this.U.U².Self}, Required: (Mon.this.U.IIsEv : -> Ev{…})
}
```

Without capture checking it compiles, and so does exporting `IIsEv` declared as a `val`. A given of a type that does
not depend on a path (`given Int`) exports. The library exports no givens: each class declares the private givens it
uses, as `Monoidal` does for its unit `I = unit.A`.

Not a bug, but costly: under capture checking, a `given` declared with an unreduced match type fails, because the check
adds a capture variable to the scrutinee; declare it in reduced form.
