# Parrot

An optimizing parser-combinator library derived from category theory.

```scala
import parrot.parser.*

final class Arithmetic(tracked val algebra: ParserAlgebra) {
  import algebra.*

  val add      = lift[(BigInt, BigInt), BigInt](_ + _)
  val subtract = lift[(BigInt, BigInt), BigInt](_ - _)
  val multiply = lift[(BigInt, BigInt), BigInt](_ * _)

  def token(s: String): P[Unit, String] = literal(s) <* spaces

  val spaces: P[Unit, String] = regex("[ ]*".r)
  val number: P[Unit, BigInt] = {
    (regex("[0-9]+".r) <* spaces).map(lift[String, BigInt](BigInt(_))).rule("number")
  }
  val (expression, product, atom) = {
    recursive[(P[Unit, BigInt], P[Unit, BigInt], P[Unit, BigInt])] { (expression, product, atom) =>
      (
        ((expression <* token("+") && product).map(add)
          |> (expression <* token("-") && product).map(subtract)
          |> product).rule("expression"),
        (product <* token("*") && atom).map(multiply) |> atom,
        number |> expression.between(token("("), token(")")),
      )
    }
  }
}

object Calculate {
  def main(args: Array[String]): Unit = {
    val parser  = StrictParser()
    val grammar = Arithmetic(parser)

    println(parser.parseAll(grammar.expression)("2 * (3 + 4)")) // Success((14,11))
    println(parser.parseAll(grammar.expression)("10 - 2 - 3"))  // Success((5,10))
  }
}
```

## Features

- Grounded in its own library of **category theory** structures, with property-checked laws
- **Parsing expression grammars (PEG)** with support for ordered choice, backtracking, lookahead, negation, repetition and recursion
- **Parser actions** as pure functions that compute results while parsing
- Parsers can depend on earlier parser results, which allows **context-sensitive parsing**
- An **optimizing parser** that normalizes parsers by utilizing structural laws and dispatches choices on the next character
- Error messages with the **furthest failure**, what was expected there and the rules around it
- **Direct and mutual left recursion** by seed growing
- Built from scratch with **no runtime dependencies**

## Usage

- Write the grammar using combinators from a `ParserAlgebra`. See [Combinators](#combinators).
- A parser `P[A, B]` consumes a prefix of the input while turning a semantic input `A` into a result `B`.
- Use `recursive` where a parser refers to itself, and `recursive[(P[…], P[…])]` for mutual recursion.
- Run the grammar on an input using an interpreter.
- `parse` and `parseAll` return the result and the offset into what was parsed, or a failure that says what was expected.
- A failure names the furthest position at which something failed, what was expected there and the rules around each expectation.

### Combinators

| Combinator                      | Syntax                                           | PEG        |
| ------------------------------- | ------------------------------------------------ | ---------- |
| Literal                         | `literal("a")`                                   | `"a"`      |
| Regular expression              | `regex("[a-z]".r)`                               | `[a-z]`    |
| Name for error messages         | `p.rule(label)`                                  | `A ← e`    |
| Pure function, identity         | `pure(f)`, `success`                             | `ε`        |
| Sequence into the next parser   | `p >> q`                                         | `e₁ e₂`    |
| Map the result, or the input    | `p.map(f)`, `p.mapInput(f)`                      |            |
| Side by side on a pair          | `p ** q`                                         |            |
| Sequence, pairing the results   | `p && q`                                         |            |
| Sequence, keeping one result    | `p *> q`, `p <* q`                               |            |
| Sequence, keeping the middle    | `p.between(open, close)`                         |            |
| Branch on a tagged input        | `p ++ q`, `p \|\| q`                             |            |
| Ordered choice                  | `p \|> q`                                        | `e₁ / e₂`  |
| Ordered choice, tagged          | `p +> q`                                         |            |
| Failure                         | `failure`                                        | `!ε`       |
| Lookahead                       | `~p`                                             | `&e`       |
| Negation                        | `!p`                                             | `!e`       |
| Optional                        | `p.?`, `p.optional`                              | `e?`       |
| Optional, as an `Option`        | `p.option`                                       | `e?`       |
| Iteration                       | `p.iterate`                                      |            |
| Repetition                      | `p.*`, `p.repeated`                              | `e*`       |
| Repetition, at least once       | `p.+`, `p.atLeastOnce`                           | `e+`       |
| Counted or separated repetition | `p.times(n)`, `p.atLeast(n)`, `p.separatedBy(q)` |            |
| Recursion                       | `recursive(p => …)`                              | `A ← e`    |

Here `p` and `q` are parsers, and `f` is a pure and total function from `lift`.

### Example: context-sensitive parsing

A parser can depend on previous results by taking the result of the parser before it as its semantic input, so what it consumes can vary with what came before.
Length-prefixed strings are an example, and their language is not context-free.
In this grammar, the parser after `>>` takes a count of the characters that follow:

```scala
final class LengthPrefixed(tracked val algebra: ParserAlgebra) {
  import algebra.*

  type State = (BigInt, String)

  val length: P[Unit, BigInt] = regex("[0-9]+".r).map(lift[String, BigInt](BigInt(_)))
  val char: P[State, String]  = regex("[a-z]".r).mapInput(lift[State, Unit](_ => ()))

  val start     = lift[BigInt, State]((_, ""))
  val countdown = lift[State, Either[String, State]]((n, s) => if n > 0 then Right((n - 1, s)) else Left(s))
  val append    = lift[(State, String), State] { case ((n, s), c) => (n, s + c) }

  val step = pure(countdown) >> (success[String] ++ (success[State] && char).map(append))

  val string: P[Unit, String] = length.map(start) >> step.iterate
}
```

`length` passes the number it read to the loop, whose state is the number of characters left and the characters read so far.
`countdown` tags the state, with `Left` and the characters at zero and `Right` with the new count otherwise, and `++` runs the parser for that side.
`iterate` repeats `step` on each `Right` and stops at a `Left`.
On `3abc`, `parseAll` returns `Success((abc,4))`, and on `2abc` it fails with `expected end of input at position 3`.

## Interpreters

- `StrictParser` is the optimizing one: it normalizes a parser into a tree of specialized nodes and runs them without allocating intermediate objects.
- `ReferenceParser` is the executable specification: it is slow and built directly as a combination of categorical structures.

`StrictParser` agrees with `ReferenceParser` on results, offsets and diagnostics, and goes beyond it on left recursion, where `ReferenceParser` fails.

## Ordered choice

The ordered choice of a parsing expression grammar is not a sum.
In `ParserAlgebra`, `|>` is the override of a classical restriction structure, which distributes over what comes before it but not over what comes after it:

```text
h >> (p |> q)  =  (h >> p) |> (h >> q)
(p |> q) >> h  ≠  (p >> h) |> (q >> h)
```

Here is a witness of the second line, in a grammar like `Arithmetic`:

```scala sketch
val (a, ab, c) = (literal("a"), literal("ab"), literal("c"))

val factored    = (a |> ab) *> c
val distributed = (a *> c) |> (ab *> c)
```

On the input `abc`, `factored` fails with `expected "c" at position 1`: `a` succeeded, so the choice committed to it and `ab` is never tried.
`distributed` succeeds, because `a *> c` fails as a whole and `ab *> c` then runs from the start.

However, the equation does hold where `h` is a pure function, which cannot fail after the choice has committed.
As an optimization, `StrictParser` uses that to rewrite `(p |> q).map(f)` to `p.map(f) |> q.map(f)`.
This allows us to merge each `map` with another potential `map`, e.g. if `p` is itself a `s.map(g)`.
Such rewrites are based on categorical laws, so they don't change what a parser does.

## Project Structure

- `parrot.category`: Categorical structures and their laws
- `parrot.parser`: `ParserAlgebra` as a direct application of the categorical structures, and implementation of the interpreters `ReferenceParser` and `StrictParser`
- `parrot.json`: `JsonGrammar`, written once against any `ParserAlgebra` and used as the end-to-end test and benchmark workload

## Future Work

- Recognize and precompile regular grammars
- Recognize and optimize tail-recursive parsers
- Implement a parsing machine interpreter
