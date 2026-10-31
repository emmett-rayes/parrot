package parrot
package category

/** A limit of a diagram *D*: **J** → **C**.
  *
  * Represents a limit (*X*, *ψ*), i.e. a cone over *D*, where
  *   - ⟨*φ*⟩: *Y* → *X* is the factorization of a cone (*Y*, *φ*) over *D*, the unique morphism with *ψ* ∘ ⟨*φ*⟩ = *φ*
  */
abstract class Limit(tracked override val D: Functor) extends Limit.Cone(D) {
  import D.F
  import D.C as J
  import D.D as C
  import C.--> as ==>
  import Limit.Cone

  /** The factorization ⟨*φ*⟩: *Y* → *X* of a cone *K* = (*Y*, *φ*) through the limit. */
  def factor(K: Cone { val D: Limit.this.D.type }): K.Apex ==> Apex

  /** Laws that any `Limit` must satisfy. */
  object LimitLaws {

    /** *ψ*_*A* ∘ ⟨*φ*⟩ = *φ*_*A*
      */
    def universal[A: J.Obj](K: Cone { val D: Limit.this.D.type })(
      using (K.Apex ==> F[A]) is Observable
    ): Boolean = {
      given (K.Apex is C.Obj) = K.apex
      (factor(K) >>> leg[A]) =?= K.leg[A]
    }

    /** ⟨*ψ* ∘ *h*⟩ = *h*: a morphism into a limit is determined by its legs. */
    def uniqueness[Y: C.Obj](h: Y ==> Apex)(using (Y ==> Apex) is Observable): Boolean = {
      factor(induced(h)) =?= h
    }
  }
}

object Limit {

  /** The limits of the diagram *F*. */
  type Of[F <: Functor] = Limit { val D: F }

  /** A cone over a diagram *D*: **J** → **C**.
    *
    * Represents a cone (*X*, *ψ*), where
    *   - *X* is the apex, an object of **C**
    *   - *ψ*_*A*: *X* → *D*[*A*] is the leg at an object *A* of **J**
    */
  abstract class Cone(tracked val D: Functor) extends caps.Pure {
    import D.{F, map}
    import D.C as J
    import D.D as C
    import J.-->
    import C.--> as ==>

    /** The apex *X*. */
    type Apex

    /** Evidence that *X* is an object of **C**. */
    def apex: Apex is C.Obj

    /** Evidence that *X* is an object, for clients of the structure. */
    given ApexIsObj: Apex is C.Obj = apex

    /** Evidence that the objects *D*[*A*] of the diagram are objects, for clients of the structure. */
    given FIsObj: [A: J.Obj] => (F[A] is C.Obj) = D.objects[A]

    /** *ψ*_*A*: *X* → *D*[*A*]
      *
      * The legs form a natural transformation from the constant functor at *X* to *D*.
      */
    def leg[A: J.Obj]: Apex ==> F[A]

    /** The cone (*Y*, *ψ* ∘ *h*) induced by a morphism *h*: *Y* → *X*. */
    final def induced[Y: C.Obj as obj](h: Y ==> Apex): Cone { val D: Cone.this.D.type; type Apex = Y } = {
      new Cone(D) {
        type Apex = Y
        def apex: Y is C.Obj             = obj
        def leg[A: J.Obj]: Apex ==> F[A] = h >>> Cone.this.leg[A]
      }
    }

    /** Laws that any `Cone` must satisfy. */
    object ConeLaws {

      /** *D*(*f*) ∘ *ψ*_*A* = *ψ*_*B*
        */
      def commutes[A: J.Obj, B: J.Obj](f: A --> B)(using (Apex ==> F[B]) is Observable): Boolean = {
        (leg[A] >>> map(f)) =?= leg[B]
      }
    }
  }
}

/** Limits of shape **J** in a category **C**.
  *
  * Represents a category **C** with limits of shape **J**, where
  *   - lim *D* is a limit of each diagram *D*: **J** → **C**
  */
abstract class Limits(tracked val J: Category, tracked val C: Category) extends caps.Pure {

  /** The limit lim *D* of a diagram *D*: **J** → **C**. */
  def limit(D: Functor { val C: J.type; val D: Limits.this.C.type }): Limit.Of[D.type]
}
