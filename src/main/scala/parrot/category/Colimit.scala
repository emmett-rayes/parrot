package parrot
package category

/** A colimit of a diagram *D*: **J** → **C**.
  *
  * Represents a colimit (*X*, *ψ*), i.e. a cocone under *D*, where
  *   - [*φ*]: *X* → *Y* is the factorization of a cocone (*Y*, *φ*) under *D*
  */
abstract class Colimit(tracked override val D: Functor, tracked override val X: D.D.Obj) extends Cocone(D, X) {
  import D.F as D
  import D.C as J
  import D.D as C
  import C.--> as ==>

  private given ApexIsObj: Apex is C.Obj = X

  private given DIsObj: [A: J.Obj] => (D[A] is C.Obj) = D.objects[A]

  /** The factorization [*φ*]: *X* → *Y* of a cocone *K* = (*Y*, *φ*) through the colimit.
    *
    * This is the unique morphism with *φ* = [*φ*] ∘ *ψ*.
    */
  def factor(K: Cocone.Of[D.type]): Apex ==> K.Apex

  /** Laws that any `Colimit` must satisfy. */
  object ColimitLaws {

    /** [*φ*] ∘ *ψ*_*A* = *φ*_*A*
      */
    def universal[A: J.Obj](K: Cocone.Of[D.type])(using (D[A] ==> K.Apex) is Observable): Boolean = {
      given (K.Apex is C.Obj) = K.X
      (leg[A] >>> factor(K)) =?= K.leg[A]
    }

    /** [*h* ∘ *ψ*] = *h*: a morphism out of a colimit is determined by its legs. */
    def uniqueness[Y: C.Obj](h: Apex ==> Y)(using (Apex ==> Y) is Observable): Boolean = {
      factor(induced(h)) =?= h
    }
  }
}

object Colimit {

  /** Refines `Colimit` to a specific functor **F**. */
  type Of[F <: Functor] = Colimit { val D: F }
}

/** Colimits of shape **J** in a category **C**.
  *
  * Represents a category **C** with colimits of shape **J**, where
  *   - colim *D* is a colimit of each diagram *D*: **J** → **C**
  */
abstract class Colimits(tracked val J: Category, tracked val C: Category) extends caps.Pure {

  /** The colimit colim *D* of a diagram *D*: **J** → **C**. */
  def colimit(D: Functor { val C: J.type; val D: Colimits.this.C.type }): Colimit.Of[D.type]
}

/** Colimits of a discrete shape **J** in a category **C**.
  *
  * Represents a category **C** with colimits of a shape **J** whose only morphisms are identities, where
  *   - Colim[*F*] is the apex of the colimit of every diagram with object map *F*
  *   - colim *G* is a colimit of each diagram *G*: **J** → **C** with object map *F*, with apex Colim[*F*]
  *
  * On a discrete shape, a diagram is determined by its objects, since a functor maps identities to identities, so the
  * apex of its colimit can be a type function of its object map. That makes the colimits of the diagrams of objects
  * *A* and *B* one type constructor, which a tensor can be ([[Coproducts.FromColimits]]).
  */
abstract class DiscreteColimits(
  tracked override val J: Category { type Self[A, B] <: A =:= B },
  tracked override val C: Category,
) extends Colimits(J, C) {

  /** The apex Colim[*F*] of the colimit of a diagram with object map *F*. */
  type Colim[F[_]]

  /** The colimit colim *G* of a diagram *G*: **J** → **C**, with apex Colim[*F*] for the object map *F* of *G*. */
  override def colimit(G: Functor { val C: DiscreteColimits.this.J.type; val D: DiscreteColimits.this.C.type })
    : Colimit.Of[G.type] { val X: Colim[G.F] is C.Obj }
}
