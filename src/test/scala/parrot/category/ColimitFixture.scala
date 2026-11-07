package parrot
package category

/** The binary coproducts of 𝒮 from its colimits of shape **2**: the points of two types, tagged by their object. */
object ColimitCoproducts extends Coproducts.FromColimits(Total.DiscreteColimits) {

  /** The name of the coproduct in law checks: the colimit Colim of the diagram (*A*,*B*). */
  given FName: TypeName[F] = TypeName("Colim")
}

/** The initial object of 𝒮 from its colimit of the empty diagram: the sum with no points. */
object ColimitInitial extends Initial.FromColimit(Total.DiscreteColimitOf(Terminal.EmptyDiagram(Total))) {

  /** The name of the initial object in law checks: the colimit Colim of the empty diagram. */
  given IName: TypeName[I] = TypeName("Colim")
}

/** 𝒮 as a cocartesian category from its discrete colimits. */
object ColimitCocartesian extends Cocartesian(Total, ColimitInitial, ColimitCoproducts)

/** The binary coproducts of 𝒫 from its colimits of shape **2**: the points of two types, tagged by their object. */
object PartialColimitCoproducts extends Coproducts.FromColimits(Partial.DiscreteColimits)

/** The initial object of 𝒫 from its colimit of the empty diagram: the sum with no points. */
object PartialColimitInitial extends Initial.FromColimit(Partial.DiscreteColimitOf(Terminal.EmptyDiagram(Partial)))

/** 𝒫 as a cocartesian category from its discrete colimits. */
object PartialColimitCocartesian extends Cocartesian(Partial, PartialColimitInitial, PartialColimitCoproducts)
