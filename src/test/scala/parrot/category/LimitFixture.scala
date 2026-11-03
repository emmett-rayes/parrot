package parrot
package category

/** The binary products of 𝒮 from its limits of shape **2**: the families of two points. */
object LimitProducts extends Products.FromLimits(Total.DiscreteLimits) {

  /** The name of the product in law checks: the limit Lim of the diagram (*A*,*B*). */
  given FName: TypeName[F] = TypeName("Lim")
}

/** The terminal object of 𝒮 from its limit of the empty diagram: the family with no points. */
object LimitTerminal extends Terminal.FromLimit(Total.DiscreteLimitOf(Terminal.EmptyDiagram(Total))) {

  /** The name of the terminal object in law checks: the limit Lim of the empty diagram. */
  given IName: TypeName[I] = TypeName("Lim")
}

/** 𝒮 as a cartesian category from its discrete limits. */
object LimitCartesian extends Cartesian(Total, LimitTerminal, LimitProducts)
