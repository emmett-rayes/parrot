package parrot
package category

/** An initial object of a category **C**.
  *
  * Represents an initial object *I*, where
  *   - ¡: *I* → *A* is the unique morphism to an object *A*
  */
abstract class Initial(tracked override val category: Category) extends Category.Object(category) {
  import category.{Obj, -->}

  /** The initial object *I*. */
  final type I = Self

  /** The unique morphism ¡: *I* → *A*. */
  def absurd[A: Obj]: I --> A

  /** The initial object as a colimit of the empty diagram, with ¡ as the factorization. */
  final lazy val colimit: Initial.AsColimit { val initial: Initial.this.type } = Initial.AsColimit(this)

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

  /** The initial objects of **K**. */
  type Of[K <: Category] = Initial { val category: K }

  /** The initial object of a category with a colimit of the empty diagram: that colimit. */
  def apply(colimits: Colimit.OfDiagram[EmptyDiagram.Of]): Of[colimits.category.type] = {
    FromColimit(colimits.colimit(EmptyDiagram(colimits.category)))
  }

  /** The initial object of a colimit *L* of the empty diagram.
    *
    * The initial object is the apex of *L*, and ¡ is the factorization through *L* of the cocone with apex *A*, which
    * has no legs.
    */
  open class FromColimit(tracked val cocone: Colimit.Of[EmptyDiagram])
      extends Initial(cocone.diagram.category) {
    import category.{Obj, -->}

    type Self = cocone.X

    def evidence: Self is Obj = {
      cocone.apex.evidence
    }

    def absurd[A: Obj]: I --> A = {
      cocone.factor(EmptyCocone(cocone.diagram, category.Object[A]))
    }
  }

  /** An initial object *I* as a colimit of the empty diagram.
    *
    * The apex of the colimit is *I*, its cocones have no legs, and the factorization of the cocone with apex *A* is ¡:
    * *I* → *A*.
    */
  final class AsColimit(tracked val initial: Initial) extends Colimit(EmptyDiagram(initial.category), initial) {
    import initial.category.-->

    def leg[A: Empty.Absurd]: Nothing --> initial.I = {
      A.absurd
    }

    def factor(cocone: Cocone.Of[diagram.type]): initial.I --> cocone.X = {
      initial.absurd[cocone.X](using cocone.apex.evidence)
    }
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
