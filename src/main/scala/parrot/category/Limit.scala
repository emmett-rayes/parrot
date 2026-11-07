package parrot
package category

/** A limit of a diagram *D*: **J** → **C**.
  *
  * Represents a limit (*X*, *ψ*), i.e. a cone over *D*, where
  *   - ⟨*φ*⟩: *Y* → *X* is the factorization of a cone (*Y*, *φ*) over *D*
  */
abstract class Limit(tracked override val diagram: Functor, tracked override val apex: diagram.target.Object)
    extends Cone(diagram, apex) {
  import diagram.F as D
  import diagram.source as J
  import diagram.target as C
  import C.--> as ==>

  /** The factorization ⟨*φ*⟩: *Y* → *X* of a cone (*Y*, *φ*) through the limit.
    *
    * This is the unique morphism with *φ* = *ψ* ∘ ⟨*φ*⟩.
    */
  def factor(cone: Cone.Over[diagram.type]): cone.X ==> X

  /** Laws that any `Limit` must satisfy. */
  object LimitLaws {
    private given XIsObj: X is C.Obj                    = apex.evidence
    private given DIsObj: [A: J.Obj] => (D[A] is C.Obj) = diagram.objects[A]

    /** *ψ*_*A* ∘ ⟨*φ*⟩ = *φ*_*A*
      */
    def universal[A: J.Obj](cone: Cone.Over[diagram.type])(using (cone.X ==> D[A]) is Observable): Boolean = {
      given (cone.X is C.Obj) = cone.apex.evidence
      (factor(cone) >>> leg[A]) =?= cone.leg[A]
    }

    /** ⟨*ψ* ∘ *h*⟩ = *h*: a morphism into a limit is determined by its legs. */
    def uniqueness[Y: C.Obj](h: Y ==> X)(using (Y ==> X) is Observable): Boolean = {
      factor(induced(h)) =?= h
    }
  }
}

object Limit {

  /** The limits of a diagram *D*. */
  type Of[D <: Functor] = Limit { val diagram: D }
}

object Limits {

  /** Limits of diagrams *D* in a category **C**. */
  abstract class InCategory(tracked val category: Category) extends caps.Pure {

    /** The type *D* of the diagrams with a limit. */
    type D <: Functor.Into[category.type]

    /** The limit of a diagram *D*. */
    def limit(diagram: D): Limit.Of[diagram.type]
  }

  /** The limits of the diagrams of type *T*[**C**] in a category **C**. */
  type OfDiagram[T[C <: Category] <: Functor.Into[C]] = InCategory { type D >: T[category.type] }

  /** Limits of the diagrams *D* of a discrete shape in a category **C**. */
  abstract class DiscreteInCategory(tracked override val category: Category) extends InCategory(category) {

    /** The type *D* of the diagrams of a discrete shape with a limit. */
    override type D <: Functor.Into[category.type] { val source: Category { type Self <: =:= } }

    /** The apex Apex[*O*,*D*] of the limit of a diagram with object map *D* on a shape with objects *O*. */
    type Apex[O <: Category.Type, D[_]]

    /** The limit of a diagram *D*, with apex Apex[*O*,*D*]. */
    override def limit(functor: D)
      : Limit.Of[functor.type] { val apex: Apex[functor.source.Obj, functor.F] is functor.target.Object }
  }

  /** The limits of the diagrams of type *T*[**C**] of a discrete shape in a category **C**. */
  type OfDiscreteDiagram[T[C <: Category] <: Functor.Into[C] { val source: Category { type Self <: =:= } }] =
    DiscreteInCategory { type D >: T[category.type] }
}
