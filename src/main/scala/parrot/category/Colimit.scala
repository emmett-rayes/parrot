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
  def factor(cocone: Cocone.Under[diagram.type]): X ==> cocone.X

  /** Laws that any `Colimit` must satisfy. */
  object ColimitLaws {

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
  }
}

object Colimit {

  /** The colimits of a diagram *D*. */
  type Of[D <: Functor] = Colimit { val diagram: D }
}

/** Colimits in a category.
  *
  * [[InCategory]] is the structure, a colimit of every diagram of a type *D*, and [[DiscreteInCategory]] refines it for
  * diagrams of a discrete shape; [[Of]] and [[OfDiscrete]] refine them to the diagrams a client needs.
  */
object Colimits {

  /** Colimits of the diagrams of type *D* in a category **C**.
    *
    * Represents a category **C** with a colimit of every diagram of type *D*, where
    *   - *D* is a type of diagrams *G*: **J** → **C**
    *   - colim *G* is a colimit of a diagram *G* of type *D*
    *
    * Colimits of the diagrams of type *D* are colimits of the diagrams of any subtype, so a client asks for the
    * diagrams it needs as a lower bound ([[Of]]), and the colimits of every diagram in 𝒮 ([[Total.Colimits]]) are its
    * colimits of the empty diagram.
    */
  abstract class InCategory(tracked val category: Category) extends caps.Pure {

    /** The type *D* of the diagrams with a colimit. */
    type D <: Functor.Into[category.type]

    /** The colimit colim *G* of a diagram *G*. */
    def colimit(diagram: D): Colimit.Of[diagram.type]
  }

  /** The colimits of the diagrams of type *T*[**C**] in a category **C**, for a type *T*[*K*] of diagrams into a
    * category *K*.
    */
  type Of[T[K <: Category] <: Functor.Into[K]] = InCategory { type D >: T[category.type] }

  /** Colimits of the diagrams of type *D* in a category **C**, of a discrete shape.
    *
    * Represents a category **C** with a colimit of every diagram of type *D*, of a shape whose only morphisms are
    * identities, where
    *   - Apex[*O*,*F*] is the apex of the colimit of every diagram with object map *F* on a shape with objects *O*
    *   - colim *G* is a colimit of a diagram *G* of type *D*, with apex Apex[*O*,*F*] for the objects *O* of its shape
    *     and its object map *F*
    *
    * A discrete shape is determined by its objects, and a diagram of it by its object map, since a functor maps
    * identities to identities, so the apex of its colimit can be a type function of both. That makes the colimits of
    * the diagrams of objects *A* and *B* one type constructor, which a tensor can be ([[Coproducts.FromColimits]]).
    */
  abstract class DiscreteInCategory(tracked override val category: Category) extends InCategory(category) {

    /** The type *D* of the diagrams with a colimit, of a discrete shape. */
    override type D <: Functor.Into[category.type] { val source: Category { type Self <: =:= } }

    /** The apex Apex[*O*,*F*] of the colimit of a diagram with object map *F* on a shape with objects *O*. */
    type Apex[O <: Category.Type, F[_]]

    /** The colimit colim *G* of a diagram *G*, with apex Apex[*O*,*F*] for the objects *O* of its shape and its
      * object map *F*.
      */
    override def colimit(functor: D)
      : Colimit.Of[functor.type] { val apex: Apex[functor.source.Obj, functor.F] is functor.target.Object }
  }

  /** The colimits of the diagrams of type *T*[**C**] in a category **C**, of a discrete shape, for a type *T*[*K*]
    * of diagrams into a category *K*.
    */
  type OfDiscrete[T[K <: Category] <: Functor.Into[K] { val source: Category { type Self <: =:= } }] =
    DiscreteInCategory { type D >: T[category.type] }
}
