# Compiled snippets of the tutorial

`check-snippets.py` extracts the Scala code blocks of the tutorial, [`docs/TUTORIAL.md`](../TUTORIAL.md), and compiles them
with Scala 3.10.0, the version of the library, and the options in `scalac-flags.txt`. The compiler is run by Scala CLI
(`scala` on the `PATH`), which downloads that version on first use, so the system's own `scalac` does not matter. Every
Scala block of the tutorial is compiled unless it is marked otherwise. The version is `SCALA_VERSION` in the script.

```sh
docs/tutorial/check-snippets.py                       # the whole document
docs/tutorial/check-snippets.py --only ch02,ch03      # some chapters (ch01 … ch22, appa … appe, preface)
docs/tutorial/check-snippets.py --classpath CP        # classpath of the compiled library, for `library` blocks
docs/tutorial/check-snippets.py --verbose             # also print why each `fails` block fails
docs/tutorial/check-snippets.py --keep DIR            # keep the compiled snippets in DIR
```

Blocks marked `library` need the compiled library: run `sbt --client compile` first and pass its classes, as in
`docs/tutorial/check-snippets.py --classpath target/out/jvm/scala-3.10.0/parrot/classes`.

It exits with status 1 if a compiled block fails to compile or a `fails` block compiles, and prints the compiler
output with line numbers translated to lines of the document.

## Conventions

The info string after ` ```scala ` selects how a block is checked:

| Info string | Meaning |
| --- | --- |
| ` ```scala ` | compiled; all such blocks of a chapter form one unit, in order |
| ` ```scala unit=NAME ` | compiled in the separate unit `NAME` of the chapter, for blocks that redefine names |
| ` ```scala fails ` | must not compile; compiled together with the preceding blocks of its unit |
| ` ```scala sketch ` | not compiled; only for another dialect, such as Stainless, and the text must say so |
| ` ```scala library ` | the unit is compiled against the library (`--classpath`) |

Options combine, as in ` ```scala unit=Separation fails `.

Each unit becomes one source file:

```
package tutorial
package chNN

object Snippets {   // or `object NAME` for `unit=NAME`
  ...the blocks, in order...
}
```

so top-level expressions and givens are legal in blocks. Units are compiled in the order in which their first block
appears, into one output directory that is on the classpath of every later unit: a chapter builds on an earlier one
by importing it, as in `import tutorial.ch03.Categories.*`. Language imports (`import language...`) are moved before
the object, after the package clauses. The checker only compiles; it does not run the code.

Parts I and II are self-contained. Parts III to V use the library through `library` blocks.
