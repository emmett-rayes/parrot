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

  private given XIsObj: X is C.Obj = apex.evidence

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

  /** Limits of the diagrams of type *D* in a category **C**.
    *
    * Represents a category **C** with a limit of each diagram of type *D*[**C**], where
    *   - lim *G* is a limit of a diagram *G* of type *D*[**C**]
    *
    * *D*[*K*] is a type of diagrams into a category *K*, and *D* is contravariant: limits of the diagrams of type *D*
    * are limits of the diagrams of any subtype, so the limits of every diagram in 𝒮 ([[Total.Limits]]) are its limits
    * of the empty diagram.
    */
  abstract class OfDiagram[-D[K <: Category] <: Functor.Into[K]](tracked val category: Category)
      extends caps.Pure {

    /** The limit lim *G* of a diagram *G*. */
    def limit(functor: D[category.type]): Limit.Of[functor.type]
  }

  /** Limits of the diagrams of type *D* in a category **C**, of a discrete shape.
    *
    * Represents a category **C** with a limit of each diagram of type *D*[**C**], of a shape whose only morphisms are
    * identities, where
    *   - Lim[*F*] is the apex of the limit of every diagram with object map *F*
    *   - lim *G* is a limit of a diagram *G* of type *D*[**C**], with apex Lim[*F*] for the object map *F* of *G*
    *
    * On a discrete shape, a diagram is determined by its objects, since a functor maps identities to identities, so the
    * apex of its limit can be a type function of its object map. That makes the limits of the diagrams of objects *A*
    * and *B* one type constructor, which a tensor can be ([[Products.FromLimits]]).
    */
  abstract class OfDiscreteDiagram[
    -D[K <: Category] <: Functor.Into[K] { val source: Category { type Self[A, B] <: A =:= B } },
  ](tracked override val category: Category)
      extends OfDiagram[D](category) {

    /** The apex Lim[*F*] of the limit of a diagram with object map *F*. */
    type Lim[F[_]]

    /** The limit lim *G* of a diagram *G*, with apex Lim[*F*] for the object map *F* of *G*. */
    override def limit(functor: D[category.type])
      : Limit.Of[functor.type] { val apex: Lim[functor.F] is functor.target.Object }
  }
}
