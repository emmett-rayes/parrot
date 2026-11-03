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

  private given XIsObj: X is C.Obj                    = apex.evidence
  private given DIsObj: [A: J.Obj] => (D[A] is C.Obj) = diagram.objects[A]

  /** The factorization ⟨*φ*⟩: *Y* → *X* of a cone *K* = (*Y*, *φ*) through the limit.
    *
    * This is the unique morphism with *φ* = *ψ* ∘ ⟨*φ*⟩.
    */
  def factor(cone: Cone.Over[diagram.type]): cone.X ==> X

  /** Laws that any `Limit` must satisfy. */
  object LimitLaws {

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

/** Limits in a category.
  *
  * [[InCategory]] is the structure, a limit of every diagram of a type *D*, and [[DiscreteInCategory]] refines it for
  * diagrams of a discrete shape; [[Of]] and [[OfDiscrete]] refine them to the diagrams a client needs.
  */
object Limits {

  /** Limits of the diagrams of type *D* in a category **C**.
    *
    * Represents a category **C** with a limit of every diagram of type *D*, where
    *   - *D* is a type of diagrams *G*: **J** → **C**
    *   - lim *G* is a limit of a diagram *G* of type *D*
    *
    * Limits of the diagrams of type *D* are limits of the diagrams of any subtype, so a client asks for the diagrams it
    * needs as a lower bound ([[Of]]), and the limits of every diagram in 𝒮 ([[Total.Limits]]) are its limits of the
    * empty diagram.
    */
  abstract class InCategory(tracked val category: Category) extends caps.Pure {

    /** The type *D* of the diagrams with a limit. */
    type D <: Functor.Into[category.type]

    /** The limit lim *G* of a diagram *G*. */
    def limit(diagram: D): Limit.Of[diagram.type]
  }

  /** The limits of the diagrams of type *T*[**C**] in a category **C**, for a type *T*[*K*] of diagrams into a
    * category *K*.
    */
  type Of[T[K <: Category] <: Functor.Into[K]] = InCategory { type D >: T[category.type] }

  /** Limits of the diagrams of type *D* in a category **C**, of a discrete shape.
    *
    * Represents a category **C** with a limit of every diagram of type *D*, of a shape whose only morphisms are
    * identities, where
    *   - Apex[*O*,*F*] is the apex of the limit of every diagram with object map *F* on a shape with objects *O*
    *   - lim *G* is a limit of a diagram *G* of type *D*, with apex Apex[*O*,*F*] for the objects *O* of its shape and
    *     its object map *F*
    *
    * A discrete shape is determined by its objects, and a diagram of it by its object map, since a functor maps
    * identities to identities, so the apex of its limit can be a type function of both. That makes the limits of the
    * diagrams of objects *A* and *B* one type constructor, which a tensor can be ([[Products.FromLimits]]).
    */
  abstract class DiscreteInCategory(tracked override val category: Category) extends InCategory(category) {

    /** The type *D* of the diagrams with a limit, of a discrete shape. */
    override type D <: Functor.Into[category.type] { val source: Category { type Self <: =:= } }

    /** The apex Apex[*O*,*F*] of the limit of a diagram with object map *F* on a shape with objects *O*. */
    type Apex[O <: Category.Type, F[_]]

    /** The limit lim *G* of a diagram *G*, with apex Apex[*O*,*F*] for the objects *O* of its shape and its object
      * map *F*.
      */
    override def limit(functor: D)
      : Limit.Of[functor.type] { val apex: Apex[functor.source.Obj, functor.F] is functor.target.Object }
  }

  /** The limits of the diagrams of type *T*[**C**] in a category **C**, of a discrete shape, for a type *T*[*K*] of
    * diagrams into a category *K*.
    */
  type OfDiscrete[T[K <: Category] <: Functor.Into[K] { val source: Category { type Self <: =:= } }] =
    DiscreteInCategory { type D >: T[category.type] }
}
