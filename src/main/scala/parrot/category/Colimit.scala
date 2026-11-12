package parrot
package category

/** A colimit of a diagram *D*: **J** → **C**.
  *
  * Represents a colimit (*X*, *ψ*), i.e. a cocone under *D*, where
  *   - [*φ*]: *X* → *Y* is the factorization of a cocone (*Y*, *φ*) under *D*
  *
  * @see docs/TUTORIAL.md §14.6
  */
abstract class Colimit(tracked override val diagram: Functor, tracked override val apex: diagram.target.Object)
    extends Cocone(diagram, apex) {
  import diagram.F as D
  import diagram.source as J
  import diagram.target as C
  import C.--> as ==>

  /** The factorization [*φ*]: *X* → *Y* of a cocone (*Y*, *φ*) through the colimit.
    *
    * This is the unique morphism with *φ* = [*φ*] ∘ *ψ*.
    */
  def factor(cocone: Cocone.Under[diagram.type]): X ==> cocone.X

  /** Laws that any `Colimit` must satisfy. */
  object ColimitLaws {
    private given XIsObj: X is C.Obj                    = apex.evidence
    private given DIsObj: [A: J.Obj] => (D[A] is C.Obj) = diagram.objects[A]

    /** [*φ*] ∘ *ψ*_*A* = *φ*_*A*
      */
    def universal[A: J.Obj](cocone: Cocone.Under[diagram.type])(using (D[A] ==> cocone.X) is Observable): Boolean = {
      given (cocone.X is C.Obj) = cocone.apex.evidence
      (leg[A] >>> factor(cocone)) =?= cocone.leg[A]
    }

    /** [*h* ∘ *ψ*] = *h*: a morphism out of a colimit is determined by its legs. */
    def uniqueness[Y: C.Obj](h: X ==> Y)(using (X ==> Y) is Observable): Boolean = {
      factor(induced(h)) =?= h
    }

    /** If *φ* = *φ*′, then [*φ*] = [*φ*′].
      *
      * @note The premise is not checked: the legs of *φ*′ must be equal to the legs of *φ* by construction.
      */
    def factorCongruence(
      cocone: Cocone.Under[diagram.type],
      cocone2: Cocone.Under[diagram.type] { val apex: cocone.apex.type },
    )(using (X ==> cocone.X) is Observable): Boolean = {
      factor(cocone) =?= factor(cocone2)
    }
  }
}

object Colimit {

  /** The colimits of a diagram *D*. */
  type Of[D <: Functor] = Colimit { val diagram: D }
}

object Colimits {

  /** Colimits of diagrams *D* in a category **C**. */
  abstract class InCategory(tracked val category: Category) extends caps.Pure {

    /** The type *D* of the diagrams with a colimit. */
    type D <: Functor.Into[category.type]

    /** The colimit of a diagram *D*. */
    def colimit(diagram: D): Colimit.Of[diagram.type]
  }

  /** The colimits of the diagrams of type *T*[**C**] in a category **C**. */
  type OfDiagram[T[C <: Category] <: Functor.Into[C]] = InCategory { type D >: T[category.type] }

  /** Colimits of the diagrams *D* of a discrete shape in a category **C**. */
  abstract class DiscreteInCategory(tracked override val category: Category) extends InCategory(category) {

    /** The type *D* of the diagrams of a discrete shape with a colimit. */
    override type D <: Functor.Into[category.type] { val source: Category { type Self <: =:= } }

    /** The apex Apex[*O*,*D*] of the colimit of a diagram with object map *D* on a shape with objects *O*. */
    type Apex[O <: Category.Type, D[_]]

    /** The colimit of a diagram *D*, with apex Apex[*O*,*D*]. */
    override def colimit(functor: D)
      : Colimit.Of[functor.type] { val apex: Apex[functor.source.Obj, functor.F] is functor.target.Object }
  }

  /** The colimits of the diagrams of type *T*[**C**] of a discrete shape in a category **C**. */
  type OfDiscreteDiagram[T[C <: Category] <: Functor.Into[C] { val source: Category { type Self <: =:= } }] =
    DiscreteInCategory { type D >: T[category.type] }
}
