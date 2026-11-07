package parrot
package category

import Category.Type
import ColimitInitial.IName

/** The laws of [[Initial]], for initial objects of a category whose objects are all types. */
abstract class InitialSpec(tracked val initial: Initial.Of[Category { type Obj = Type }])(using
  category: CategoryFixture.For[initial.category.type],
  typename: TypeName[initial.I],
  types: SampleTypes,
  sample: Sample[initial.I],
) extends LawSuite("Initial", s"${typename.name} on ${category.name}") {
  import types.{T1, given}
  import category.*
  import initial.category.-->
  import initial.I
  import initial.InitialLaws.*

  law("uniqueness") {
    val observations = observe[I, T1]
    val fs           = arrow[I, T1]

    forAll(observations, fs) { (observe, f) =>
      given ((I --> T1) is Observable) = observe
      uniqueness(f)
    }
  }
}

class ScalaNothingIsInitialTest   extends InitialSpec(Total.NothingIsInitial)
class PartialNothingIsInitialTest extends InitialSpec(Partial.NothingIsInitial)
class TotalColimitIsInitialTest   extends InitialSpec(ColimitInitial)
class PartialColimitIsInitialTest extends InitialSpec(PartialColimitInitial)
