package parrot
package category

import org.scalacheck.Gen

/** The laws of [[Observable]], for the observations of a fixture's arrows *T1* → *T2*, sampled afresh for every case.
  * Pairs and triples are sampled so that agreeing arrows occur often: an arrow, its variant and the variant of that.
  */
abstract class ObservableSpec(F: CategoryFixture)(using types: SampleTypes) extends LawSuite("Observable", F.name) {
  import types.{T1, T2, given}
  import F.K.-->

  private lazy val observations: Gen[(T1 --> T2) is Observable] = F.observe[T1, T2]

  private lazy val arrows: Gen[T1 --> T2] = F.arrow[T1, T2]

  private lazy val pairs: Gen[(T1 --> T2, T1 --> T2)] = {
    Gen.oneOf(Gen.zip(arrows, arrows), arrows.map(f => (f, F.variant(f))))
  }

  law("reflexivity") {
    forAll(observations, arrows)((o, f) => o.ObservableLaws.reflexivity(f))
  }

  law("symmetry") {
    forAll(observations, pairs) { case (o, (f, g)) => o.ObservableLaws.symmetry(f, g) }
  }

  law("transitivity") {
    forAll(observations, pairs, Gen.oneOf(true, false)) { case (o, (f, g), same) =>
      o.ObservableLaws.transitivity(f, g, if same then F.variant(g) else f)
    }
  }

  law("soundness") {
    forAll(observations, arrows)((o, f) => o.ObservableLaws.soundness(f, F.variant(f)))
  }
}

class TotalIsObservableTest extends ObservableSpec(TotalFixture) {
  import Total.>>>

  counterexample("congruence", "precomposition leaves the sample points") {
    forAll(Sample.points[Int], TotalFixture.arrow[Int, String], TotalFixture.arrow[Int, Int]) { (points, f, h) =>
      given ((Int -> String) is Observable) = Observable.total(points)
      val g: Int -> String                  = x => if points.contains(x) then f(x) else f(x) + "!"
      !(f =?= g) || ((h >>> f) =?= (h >>> g))
    }
  }
}

class PartialIsObservableTest     extends ObservableSpec(PartialFixture)
class StringStateIsObservableTest extends ObservableSpec(StringStateFixture.category)
