package parrot
package category

import Category.Type
import LimitTerminal.IName

/** The laws of [[Terminal]], for terminal objects of a category whose objects are all types. */
abstract class TerminalSpec(tracked val terminal: Terminal { val category: Category { type Obj = Type } })(using
  category: CategoryFixture.For[terminal.category.type],
  typename: TypeName[terminal.I],
  types: SampleTypes,
  sample: Sample[terminal.I],
) extends LawSuite("Terminal", s"${typename.name} on ${category.name}") {
  import types.{T1, given}
  import category.*
  import terminal.category.-->
  import terminal.I
  import terminal.TerminalLaws.*

  law("uniqueness") {
    val observations = observe[T1, I]
    val fs           = arrow[T1, I]

    forAll(observations, fs) { (observe, f) =>
      given ((T1 --> I) is Observable) = observe
      uniqueness(f)
    }
  }
}

class ScalaUnitIsTerminalTest  extends TerminalSpec(Total.UnitIsTerminal)
class TotalLimitIsTerminalTest extends TerminalSpec(LimitTerminal)
