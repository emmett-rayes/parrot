package parrot
package category

import org.scalacheck.Gen

import Sample.given
import Category.Type

/** The laws of [[Recursion]]: those of [[GuardedRecursion]], with functions that recurse on smaller arguments. */
abstract class RecursionSpec(
  name: String,
  tracked override val recursion: Recursion.On[Promonad.On[Category { type Obj = Type }]],
  structure: String = "Recursion",
)(using
  promonad: PromonadFixture.For[recursion.promonad.type],
  types: SampleTypes,
) extends GuardedRecursionSpec(name, recursion, structure)

// ==== 𝒫 ====

class PartialKnotsIsRecursionTest extends RecursionSpec("Partial (knots)", Partial.Knots) {
  def guarded[B: Sample]: Gen[(Int ~> B) -> (Int ~> B)] = {
    for {
      base    <- Sample.function[Int, B]
      go      <- Sample.function[Int, Boolean]
      k       <- Sample.function[Int, Int]
      combine <- Sample.function[(Int, B), B]
    } yield (rec: Int ~> B) =>
      Partial(x => if x == 0 || !go(x) then base(x) else combine((x, rec.run(Descent.below(x, k(x))))))
  }
}
