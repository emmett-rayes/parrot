package parrot
package category

/** The binary coproducts of 𝒮 from its colimits of shape **2**: the points of two types, tagged by their object. */
object ColimitCoproducts extends Coproducts.FromColimits(Total.DiscreteColimitsOf(Category.Discrete2))

/** The initial object of 𝒮 from its colimit of the empty diagram: the sum with no points. */
object ColimitInitial extends Initial.FromColimit(Total.DiscreteColimitOf(Terminal.EmptyDiagram(Total))) {

  /** The name of the initial object in law checks: the colimit Colim of the empty diagram. */
  given IName: TypeName[I] = TypeName("Colim")
}

/** 𝒮 as a cocartesian category from its discrete colimits. */
object ColimitCocartesian extends Cocartesian(Total, ColimitInitial, ColimitCoproducts)
