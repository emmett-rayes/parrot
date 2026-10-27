package parrot
package category

import scala.compiletime.deferred

/** The types at which the generic specs check their laws: four types with their samples.
  *
  * A spec takes a bundle as a context parameter and checks its laws at *T1*, …, *T4*, so that the same laws can be
  * checked at other types by passing another bundle. The samples are deferred givens: a bundle only fixes its types,
  * and their samples are found where it does.
  */
trait SampleTypes extends caps.Pure {
  type T1
  type T2
  type T3
  type T4

  /** How to sample values of *T1*. */
  given T1Sample: Sample[T1] = deferred

  /** How to sample values of *T2*. */
  given T2Sample: Sample[T2] = deferred

  /** How to sample values of *T3*. */
  given T3Sample: Sample[T3] = deferred

  /** How to sample values of *T4*. */
  given T4Sample: Sample[T4] = deferred
}

object SampleTypes {

  /** `Int`, `String`, `Boolean` and `Long`: four distinct types with cheap samples, so that a law that confuses two of
    * them does not compile. The bundle of every spec unless a test passes another one.
    */
  given Standard: SampleTypes {
    type T1 = Int
    type T2 = String
    type T3 = Boolean
    type T4 = Long
  }
}
