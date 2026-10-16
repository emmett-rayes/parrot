package parrot
package parser

import category.*
import category.Enriched.over
import category.Profunctor.on

import scala.util.Try

/** A [[ParserAlgebra]] interpreter using the [[Kleisli]] promonad over a [[StateT]] monad. */
trait KleisliParser extends ParserAlgebra,
      Sequencing,
      Zipping,
      Branching,
      Alternation,
      Lookahead,
      Repetition,
      Recursion,
      Pairing,
      Iteration {

  type Input
  type ParserM = StateT[Input, Try]

  type On          = Function
  type Self        = Kleisli[ParserM]
  type Empty       = Unit
  type Pair        = Tuple2
  type None        = Nothing
  type Alternative = Either

  import StateT.given

  override val OnIsCartesian: Cartesian.FunctionIsCartesian.type = RepetitionOnCartesian
  
  override given RepetitionOnCartesian: Cartesian.FunctionIsCartesian.type         = Cartesian.FunctionIsCartesian
  override given RepetitionOnCocartesian: Cocartesian.FunctionIsCocartesian.type   = Cocartesian.FunctionIsCocartesian
  override given PairingOnCartesian: Cartesian.FunctionIsCartesian.type            = Cartesian.FunctionIsCartesian
  override given SequencingPromonad: Self is Promonad on Function                  = Kleisli.KleisliIsPromonad
  override given ZippingStrong: Self is Strong.on[Function, Unit, Tuple2]          = Kleisli.KleisliIsStrong
  override given AlternationEnriched: Self is Enriched over Monoid.Additive        = Kleisli.KleisliIsValuedEnriched
  override given LookaheadRestriction: Self is Restriction                         = Kleisli.KleisliIsRestriction
  override given IterationElgot: Self is Elgot.`with`[Nothing, Either]             = Kleisli.KleisliIsElgot
  override given BranchingCocartesian: Self is Cocartesian.`with`[Nothing, Either] = Kleisli.KleisliIsCocartesian
  override given RecursionEnriched: Self is Enriched over Fixed.in[Function, Unit, LazyTuple2, Function] =
    Kleisli.KleisliIsFixedEnriched
}
