package parrot
package category

/** A limit of a diagram *D*: **J** → **C**.
  *
  * Represents a limit (*X*, *ψ*), i.e. a cone over *D*, where
  *   - ⟨*φ*⟩: *Y* → *X* is the factorization of a cone (*Y*, *φ*) over *D*
  */
abstract class Limit(tracked override val D: Functor, tracked override val X: D.D.Object) extends Cone(D, X) {
  import D.F as D
  import D.C as J
  import D.D as C
  import C.--> as ==>

  private given ApexIsObj: Apex is C.Obj = X.U

  private given DIsObj: [A: J.Obj] => (D[A] is C.Obj) = D.objects[A]

  /** The factorization ⟨*φ*⟩: *Y* → *X* of a cone *K* = (*Y*, *φ*) through the limit.
    *
    * This is the unique morphism with *φ* = *ψ* ∘ ⟨*φ*⟩.
    */
  def factor(K: Cone.Of[D.type]): K.Apex ==> Apex

  /** Laws that any `Limit` must satisfy. */
  object LimitLaws {

    /** *ψ*_*A* ∘ ⟨*φ*⟩ = *φ*_*A*
      */
    def universal[A: J.Obj](K: Cone.Of[D.type])(using (K.Apex ==> D[A]) is Observable): Boolean = {
      given (K.Apex is C.Obj) = K.X.U
      (factor(K) >>> leg[A]) =?= K.leg[A]
    }

    /** ⟨*ψ* ∘ *h*⟩ = *h*: a morphism into a limit is determined by its legs. */
    def uniqueness[Y: C.Obj](h: Y ==> Apex)(using (Y ==> Apex) is Observable): Boolean = {
      factor(induced(h)) =?= h
    }
  }
}

object Limit {

  /** Refines `Limit` to a specific functor **F**. */
  type Of[F <: Functor] = Limit { val D: F }

  /** Limits of the diagrams of type *D* in a category **C**.
    *
    * Represents a category **C** with a limit of each diagram of type *D*[**C**], where
    *   - lim *G* is a limit of a diagram *G* of type *D*[**C**]
    *
    * *D*[*K*] is a type of diagrams into a category *K*, and *D* is contravariant: limits of the diagrams of type *D*
    * are limits of the diagrams of any subtype, so the limits of every diagram in 𝒮 ([[Total.Limits]]) are its limits
    * of the empty diagram.
    */
  abstract class OfDiagram[-D[K <: Category] <: Functor { val D: K }](tracked val C: Category) extends caps.Pure {

    /** The limit lim *G* of a diagram *G*. */
    def limit(G: D[C.type]): Limit.Of[G.type]
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
    -D[K <: Category] <: Functor { val C: Category { type Self[A, B] <: A =:= B }; val D: K },
  ](tracked override val C: Category)
      extends OfDiagram[D](C) {

    /** The apex Lim[*F*] of the limit of a diagram with object map *F*. */
    type Lim[F[_]]

    /** The limit lim *G* of a diagram *G*, with apex Lim[*F*] for the object map *F* of *G*. */
    override def limit(G: D[C.type]): Limit.Of[G.type] { val X: G.D.ObjectOf[Lim[G.F]] }
  }
}
