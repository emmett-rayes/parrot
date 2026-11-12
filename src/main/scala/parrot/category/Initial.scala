package parrot
package category

/** An initial object of a category **C**.
  *
  * Represents an initial object *I*, where
  *   - ¡: *I* → *A* is the unique morphism to an object *A*
  *
  * @see docs/TUTORIAL.md §14.1
  */
abstract class Initial(tracked override val category: Category) extends Category.Object(category) {
  import category.{Obj, -->}

  /** The initial object *I*. */
  final type I = Self

  /** The unique morphism ¡: *I* → *A*. */
  def absurd[A: Obj]: I --> A

  /** The initial object as a colimit of the empty diagram, with ¡ as the factorization of a cocone with no legs. */
  final lazy val asColimit: Initial.AsColimit.Of[this.type] = Initial.AsColimit(this)

  /** The initial object as a terminal object of **C**ᵒᵖ, with ¡ as !. */
  final lazy val op: Initial.Op.Of[this.type] = Initial.Op(this)

  /** Laws that any `Initial` must satisfy. */
  object InitialLaws {

    /** *f* = ¡ for every *f*: *I* → *A*
      */
    def uniqueness[A: Obj](f: I --> A)(using (I --> A) is Observable): Boolean = {
      f =?= absurd[A]
    }
  }
}

object Initial {
  import Category.Empty
  import Terminal.EmptyDiagram

  /** The initial objects of a category **C**. */
  type Of[C <: Category] = Initial { val category: C }

  /** The initial object of a category with colimits of the diagrams of shape **0**. */
  def apply(colimits: Colimits.OfDiagram[EmptyDiagram.Into]): Of[colimits.category.type] = {
    FromColimit(colimits.colimit(EmptyDiagram(colimits.category)))
  }

  /** The initial object from a colimit *L* of the empty diagram.
    *
    * The initial object is the apex of *L*, and ¡: *I* → *A* is the factorization through *L* of the cocone with apex
    * *A* and no legs.
    */
  open class FromColimit(tracked val colimit: Colimit.Of[EmptyDiagram]) extends Initial(colimit.diagram.category) {
    import category.{Obj, -->}

    type Self = colimit.X

    def evidence: Self is Obj = {
      colimit.apex.evidence
    }

    def absurd[A: Obj]: I --> A = {
      colimit.factor(EmptyCocone(colimit.diagram, category.Object[A]))
    }
  }

  /** An initial object *I* as a colimit of the empty diagram.
    *
    * The apex of the colimit is *I*, it has no legs, and the factorization of the cocone with apex *A* is ¡: *I* → *A*.
    */
  final class AsColimit(tracked val initial: Initial) extends Colimit(EmptyDiagram(initial.category), initial) {
    import initial.category.-->

    def leg[A: Empty.Absurd]: Nothing --> initial.I = {
      A.absurd
    }

    def factor(cocone: Cocone.Under[diagram.type]): initial.I --> cocone.X = {
      initial.absurd[cocone.X](using cocone.apex.evidence)
    }
  }

  object AsColimit {

    /** The initial object *I* as a colimit of the empty diagram. */
    type Of[I <: Initial] = AsColimit { val initial: I }
  }

  /** An initial object *I* of a category **C**, as a terminal object of **C**ᵒᵖ: ! is ¡. */
  final class Op(tracked val initial: Initial) extends Terminal(initial.category.op) {
    import category.{Obj, -->}

    type Self = initial.I

    def evidence: Self is Obj = {
      initial.evidence
    }

    def discard[A: Obj]: A --> I = {
      initial.absurd[A]
    }
  }

  object Op {

    /** The initial object *T* as a terminal object of the opposite category. */
    type Of[T <: Initial] = Op { val initial: T }
  }

  /** The cocone with apex *X* under a diagram of the empty shape.
    *
    * The empty cocone has no legs.
    */
  final class EmptyCocone(
    tracked override val diagram: Functor { val source: Empty.type },
    tracked override val apex: diagram.target.Object,
  ) extends Cocone(diagram, apex) {
    import diagram.target.-->

    def leg[A: Empty.Absurd]: diagram.F[A] --> X = {
      A.absurd
    }
  }
}
