package parrot
package category

/** A terminal object of a category **C**.
  *
  * Represents a terminal object *I*, where
  *   - !: *A* → *I* is the unique morphism from an object *A*
  */
abstract class Terminal(tracked override val category: Category, tracked override val evidence: category.Obj)
    extends Category.Object(category, evidence) {
  import category.{Obj, -->}

  /** The terminal object *I*. */
  final type I = evidence.Self

  /** The unique morphism !: *A* → *I*. */
  def discard[A: Obj]: A --> I

  /** The terminal object as a limit of the empty diagram, with ! as the factorization. */
  final lazy val limit: Terminal.AsLimit { val terminal: Terminal.this.type } = Terminal.AsLimit(this)

  /** Laws that any `Terminal` must satisfy. */
  object TerminalLaws {

    /** *f* = ! for every *f*: *A* → *I*
      */
    def uniqueness[A: Obj](f: A --> I)(using (A --> I) is Observable): Boolean = {
      f =?= discard[A]
    }
  }
}

object Terminal {
  import Category.Empty

  /** The terminal objects of **K**. */
  type Of[K <: Category] = Terminal { val category: K }

  /** The terminal object of a category with a limit of the empty diagram: that limit. */
  def apply(limits: Limit.OfDiagram[EmptyDiagram.Of]): Of[limits.category.type] = {
    FromLimit(limits.limit(EmptyDiagram(limits.category)))
  }

  /** The terminal object of a limit *L* of the empty diagram.
    *
    * The terminal object is the apex of *L*, and ! is the factorization through *L* of the cone with apex *A*, which
    * has no legs.
    */
  open class FromLimit(tracked val cone: Limit.Of[EmptyDiagram])
      extends Terminal(cone.diagram.category, cone.apex.evidence) {
    import category.{Obj, -->}

    def discard[A: Obj]: A --> I = {
      cone.factor(EmptyCone(cone.diagram, category.Object[A]))
    }
  }

  /** A terminal object *T* as a limit of the empty diagram.
    *
    * The apex of the limit is *I*, its cones have no legs, and the factorization of the cone with apex *A* is !: *A* →
    * *I*.
    */
  final class AsLimit(tracked val terminal: Terminal) extends Limit(EmptyDiagram(terminal.category), terminal) {
    import terminal.category.-->

    def leg[A: Empty.Absurd]: terminal.I --> Nothing = {
      A.absurd
    }

    def factor(cone: Cone.Of[diagram.type]): cone.X --> terminal.I = {
      terminal.discard[cone.X](using cone.apex.evidence)
    }
  }

  /** The cone with apex *X* over a diagram of the empty shape.
    *
    * The empty cone has no legs.
    */
  final class EmptyCone(
    tracked override val diagram: Functor { val source: Empty.type },
    tracked override val apex: diagram.target.Object,
  ) extends Cone(diagram, apex) {
    import diagram.target.-->

    def leg[A: Empty.Absurd]: X --> diagram.F[A] = {
      A.absurd
    }
  }

  /** The empty diagram **0** → **K**, the unique functor out of the empty category.
    */
  final class EmptyDiagram(tracked val category: Category) extends Functor(Empty, category) {
    import category.--> as ==>
    import Empty.{Absurd, -->}

    type Self[A] = Nothing

    def objects[A: Absurd]: Nothing is category.Obj = {
      A.absurd
    }

    def map[A: Absurd, B: Absurd](f: A --> B): Nothing ==> Nothing = {
      A.absurd
    }
  }

  object EmptyDiagram {

    /** Refines `EmptyDiagram` to a specific category **K**. */
    type Of[K <: Category] = EmptyDiagram { val category: K }
  }
}
