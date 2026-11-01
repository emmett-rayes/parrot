package parrot
package category

import Category.Type

/** The laws of [[Terminal]], for terminal objects of a category whose objects are all types. */
abstract class TerminalSpec(tracked val T: Terminal { val C: Category { type Obj = Type } })(using
  category: CategoryFixture.On[T.C.type],
  typename: TypeName[T.I],
  types: SampleTypes,
  sample: Sample[T.I],
) extends LawSuite("Terminal", s"${typename.name} on ${category.name}") {
  import types.{T1, given}
  import category.*
  import T.C.-->
  import T.I
  import T.TerminalLaws.*

  law("uniqueness") {
    val observations = observe[T1, I]
    val fs           = arrow[T1, I]

    forAll(observations, fs) { (observe, f) =>
      given ((T1 --> I) is Observable) = observe
      uniqueness(f)
    }
  }
}

class ScalaUnitIsTerminalTest extends TerminalSpec(Total.UnitIsTerminal)
