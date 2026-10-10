# StrictParser optimizations

`StrictParser` interprets `ParserAlgebra` with reified parser terms (`Node`) over reified pure functions (`Fn`),
normalized at construction time and run against a single mutable `State`.

## 1. Reified, normalizing pure functions (`Fn`)

- Structural functions are data, not closures, so smart constructors can inspect them: identity, projections, pairing,
  injections, copairing and `!` (discarding the input).
- Composition normalizes:
  - *id* ⨾ *f* = *f* = *f* ⨾ *id*
  - ⟨*f*, *g*⟩ ⨾ *π*₁ = *f* and ⟨*f*, *g*⟩ ⨾ *π*₂ = *g*
  - *ι*₁ ⨾ [*f*, *g*] = *f* and *ι*₂ ⨾ [*f*, *g*] = *g*
  - *f* ⨾ ! = !
  - two `Lift`s fuse into one closure
  - compositions re-associate to the right
- Pairing and copairing normalize: ⟨*π*₁, *π*₂⟩ = *id* and [*ι*₁, *ι*₂] = *id*.

## 2. Construction-time fusion (`sequence`)

- `Success` is removed on either side of `>>`; `Failure >> p` becomes `Failure`.
- Two adjacent `Pure`s merge into one `Pure`.
- Δ ⨾ `Zip(p, q)` becomes `Pair(p, q)`, so the input is never duplicated into a tuple.
- `Pair(p, q)` followed by π₁ or π₂ becomes `ThenSkip` or `SkipThen`, so no result tuple is built.
- `Branch(p, q)` followed by [*f*, *g*] becomes `Merge(p ⨾ f, q ⨾ g)`, so no intermediate `Either` is built.
- A pure step after a choice is pushed into each alternative, (*p* | *q*) ⨾ *f* = (*p* ⨾ *f*) | (*q* ⨾ *f*). This is sound
  because pure functions are total. Combined with `Fn` normalization, `(p or q).map([f, g])` becomes
  `p.map(f) orElse q.map(g)` with no `Either`.
- Sequences re-associate to the right, so redexes surface at the head.

## 3. Other smart constructors

- `zip(success)` becomes `First(p)`.
- `pure(id)` becomes `Success`.
- `lookahead` of `Success`/`Pure` becomes `Success`, and `lookahead(lookahead(p))` becomes `lookahead(p)`.
- `not(failure)` becomes `Success`.
- Choice:
  - nested choices are flattened into one n-ary `Choice`
  - `Failure` alternatives are dropped
  - alternatives after one that always succeeds (`Success`/`Pure`) are dropped
  - a choice with 0 or 1 alternatives collapses to `Failure` or to that alternative

## 4. Dedicated nodes instead of generic derivations

- `Pair`, `SkipThen`, `ThenSkip`, `First` and `Merge` run directly, without tuples or `Either`.
- `Not` is a single node rather than the derived `(~p +> success) >> (failure || success)`.
- `Repeat(p, min, max, separator)` implements `repeated`, `times`, `atLeast` and `separatedBy` as one loop, instead of
  `loop` over tuples and `Either`.
- `Loop` is a `while` loop.

## 5. Static analysis and first-character dispatch

- `Info(first, nullable)` is computed per node: the characters a node can start with, and whether it may succeed
  without consuming anything.
- Recursive knots are solved by Kleene iteration from "never succeeds", so left recursion is handled too. Results for
  closed knots are cached on the `Rec` node.
- Each `Choice` lazily builds a `Dispatch` table:
  - candidate alternatives per ASCII character, plus one list for non-ASCII characters and one for end of input
  - alternatives that cannot succeed on the next character are skipped without being run
- When the first alternative is skipped, its failure label is still recorded, so error reporting stays close to the
  reference interpreter.

## 6. Lexical primitives

- **Regex compilation** (`Scanner`): regexes that are concatenations of single-character atoms, optionally quantified
  with `?`, `*` or `+`, run on a `Scanner` instead of `java.util.regex`.
  - Atoms are literal characters, escapes, `.` and character classes.
  - Examples: `[0-9]+`, `[1-9][0-9]*`, `[^"\\\u0000-\u001f]+`, `(?s).`
  - Matching is greedy and possessive over `CharSet`s with an ASCII bitmask.
  - A regex is only compiled when every quantified atom is disjoint from all later atoms, so possessive matching agrees
    with backtracking.
- **Matcher reuse**: other regexes reuse one `Matcher` per pattern per run.
- **Literals**: the first character is checked before the full comparison, so a one-character literal costs a single
  `charAt`.
- **Failure labels** are computed once, at construction time.

## 7. Runtime representation

- A single mutable `State` per run holds the offset, the furthest failure and the expected label. Backtracking only
  resets an `Int`.
- Results are unboxed: `Out[B]` is an opaque type over `B` with a failure sentinel. Successes and failures allocate
  nothing.

## 8. Recursion

- `recursive` ties a `Rec` knot once, instead of re-applying a fixed-point combinator.
- Left recursion is handled by seed growing (Warth et al.) without a memo table. Only active recursive calls are
  tracked, on a stack of `Head`s in `State`.
- Parsers that are not left-recursive pay one push and one pop per recursive call.

## Categorical structure

`StrictParser` provides the same structures as `ReferenceParser`. They are implemented by its smart constructors, so the
laws are checked against the optimized implementation (`StrictParserLawsTest`, extensional equality on sampled semantic
inputs and sources):

| Given                     | Structure                                | Implemented by               |
|---------------------------|------------------------------------------|------------------------------|
| `NodeIsPromonad`          | `Promonad` on `Fn`                       | `pure`, `success`, `andThen` |
| `NodeIsStrong`            | `Strong` on (`Fn`, `Unit`, `Tuple2`)     | `zip` with `success`         |
| `NodeIsCocartesian`       | `Cocartesian` (`Nothing`, `Either`)      | `Inl`/`Inr`, `merge`, `branch` |
| `NodeIsAdditiveEnriched`  | `Enriched` over `Monoid.Additive`        | `failure`, `orElse`          |
| `NodeIsRestriction`       | `Restriction`                            | `lookahead`                  |
| `NodeIsElgot`             | `Elgot` (`Nothing`, `Either`)            | `loop`                       |
| `NodeIsFixedEnriched`     | `Enriched` over `Fixed`                  | `recursive`                  |

The laws hold except for these, each pinned down by a counterexample test:
- parsers are premonoidal, so interchange fails;
- composition distributes over choice only on the right;
- seed-grown fixed points of left-recursive definitions break the fixed-point law.

## Deliberately not done

- No packrat memoization: `rule` only relabels failures.
- No type-level strict unit, which is unsound for parametric code. Term-level normalization of structural morphisms is
  equivalent by Mac Lane's coherence theorem.

## Deviations from the reference interpreter

- A repetition stops after an iteration that consumes nothing; the reference diverges.
- Left recursion succeeds by seed growing; the reference diverges. Seed growing breaks the Conway laws when the
  definition is non-monotone (ordered choice, negation).
- When several failures happen at the same furthest position, the reported expectation may differ.

## Measured effect

`sbt "Test/runMain parrot.parser.JsonBenchmark [--reference] [suite ...]"` runs four suites one after the other, each
reported separately with its own methodology:

- **JSONTestSuite**: the `test_parsing` fixtures of [nst/JSONTestSuite](https://github.com/nst/JSONTestSuite).
- **json-dummy-data**: the documents of [json-dummy-data](https://microsoftedge.github.io/Demos/json-dummy-data).
- **json_benchmark**: the documents of [TkTech/json_benchmark](https://github.com/TkTech/json_benchmark), up to 66 MB.
- **nativejson-benchmark**: the Parse and Parse Validation benchmarks of
  [miloyip/nativejson-benchmark](https://github.com/miloyip/nativejson-benchmark).

The first two suites are vendored in `src/test/resources/json`. The last two are downloaded from pinned commits into
`target/benchmark-data`. `--reference` adds `ReferenceParser` as the baseline. Memory is the heap allocated by the
parsing thread, including the parse trees.

nativejson-benchmark Parse (canada, citm_catalog, twitter: 4.6 MB, minimum of 10 trials):

| Interpreter       | Throughput  | Allocated per byte | vs `ReferenceParser`              |
|-------------------|-------------|--------------------|-----------------------------------|
| `ReferenceParser` | 6.6 MiB/s   | 724 B              | 1.0×                              |
| `StrictParser`    | 126.4 MiB/s | 16.5 B             | 19× throughput, 1/44 allocation   |

Both interpreters pass all 34 JSON_checker validation cases.

`ReferenceFnParser` uses `Fn` without `StrictParser`'s normalization and analysis. In an earlier measurement it ran at
0.9× the throughput of `ReferenceParser`, so `Fn` alone gives no speedup. `Fn` matters because it makes structural
morphisms visible to the smart constructors.
