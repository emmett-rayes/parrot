package parrot
package category

/** A colimit of a diagram *D*: **J** → **C**.
  *
  * Represents a colimit (*X*, *ψ*), i.e. a cocone under *D*, where
  *   - [*φ*]: *X* → *Y* is the factorization of a cocone (*Y*, *φ*) under *D*
  */
abstract class Colimit(tracked override val diagram: Functor, tracked override val apex: diagram.target.Object)
    extends Cocone(diagram, apex) {
  import diagram.F as D
  import diagram.source as J
  import diagram.target as C
  import C.--> as ==>

  private given XIsObj: X is C.Obj = apex.evidence

  private given DIsObj: [A: J.Obj] => (D[A] is C.Obj) = diagram.objects[A]

  /** The factorization [*φ*]: *X* → *Y* of a cocone *K* = (*Y*, *φ*) through the colimit.
    *
    * This is the unique morphism with *φ* = [*φ*] ∘ *ψ*.
    */
  def factor(cocone: Cocone.Of[diagram.type]): X ==> cocone.X

  /** Laws that any `Colimit` must satisfy. */
  object ColimitLaws {

    /** [*φ*] ∘ *ψ*_*A* = *φ*_*A*
      */
    def universal[A: J.Obj](cocone: Cocone.Of[diagram.type])(using (D[A] ==> cocone.X) is Observable): Boolean = {
      given (cocone.X is C.Obj) = cocone.apex.evidence
      (leg[A] >>> factor(cocone)) =?= cocone.leg[A]
    }

    /** [*h* ∘ *ψ*] = *h*: a morphism out of a colimit is determined by its legs. */
    def uniqueness[Y: C.Obj](h: X ==> Y)(using (X ==> Y) is Observable): Boolean = {
      factor(induced(h)) =?= h
    }
  }
}

object Colimit {

  /** Refines `Colimit` to a specific functor **F**. */
  type Of[F <: Functor] = Colimit { val diagram: F }

  /** Colimits of the diagrams of type *D* in a category **C**.
    *
    * Represents a category **C** with a colimit of each diagram of type *D*[**C**], where
    *   - colim *G* is a colimit of a diagram *G* of type *D*[**C**]
    *
    * *D*[*K*] is a type of diagrams into a category *K*, and *D* is contravariant: colimits of the diagrams of type *D*
    * are colimits of the diagrams of any subtype, so the colimits of every diagram in 𝒮 ([[Total.Colimits]]) are its
    * colimits of the empty diagram.
    */
  abstract class OfDiagram[-D[K <: Category] <: Functor { val target: K }](tracked val category: Category)
      extends caps.Pure {

    /** The colimit colim *G* of a diagram *G*. */
    def colimit(functor: D[category.type]): Colimit.Of[functor.type]
  }

  /** Colimits of the diagrams of type *D* in a category **C**, of a discrete shape.
    *
    * Represents a category **C** with a colimit of each diagram of type *D*[**C**], of a shape whose only morphisms are
    * identities, where
    *   - Colim[*F*] is the apex of the colimit of every diagram with object map *F*
    *   - colim *G* is a colimit of a diagram *G* of type *D*[**C**], with apex Colim[*F*] for the object map *F* of *G*
    *
    * On a discrete shape, a diagram is determined by its objects, since a functor maps identities to identities, so the
    * apex of its colimit can be a type function of its object map. That makes the colimits of the diagrams of objects
    * *A* and *B* one type constructor, which a tensor can be ([[Coproducts.FromColimits]]).
    */
  abstract class OfDiscreteDiagram[
    -D[K <: Category] <: Functor { val source: Category { type Self[A, B] <: A =:= B }; val target: K },
  ](tracked override val category: Category)
      extends OfDiagram[D](category) {

    /** The apex Colim[*F*] of the colimit of a diagram with object map *F*. */
    type Colim[F[_]]

    /** The colimit colim *G* of a diagram *G*, with apex Colim[*F*] for the object map *F* of *G*. */
    override def colimit(functor: D[category.type])
      : Colimit.Of[functor.type] { val apex: functor.target.ObjectOf[Colim[functor.F]] }
  }
}
