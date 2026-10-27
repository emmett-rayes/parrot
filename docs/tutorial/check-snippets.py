#!/usr/bin/env python3
"""Compiles the Scala code blocks of the tutorial, so that every snippet is checked by the compiler.

Usage:
    docs/tutorial/check-snippets.py [--document FILE] [--classpath CP] [--only ch02,ch03,...] [--keep DIR] [--verbose]

Conventions (see docs/tutorial/README.md):
    ```scala                 compiled; all such blocks of a chapter form one unit, `object Snippets`
    ```scala unit=NAME       compiled in the separate unit NAME of the chapter, `object NAME`
    ```scala fails           must not compile, together with the preceding blocks of its unit
    ```scala sketch          not compiled (another dialect, such as Stainless)
    ```scala library         the unit is compiled against the library (`--classpath`)

Every unit becomes one file:

    package tutorial
    package chNN

    object Snippets {   // or object NAME
      ...blocks, in order...
    }

Units are compiled in the order in which their first block appears, into one output directory that is on the
classpath of every later unit, so a chapter can import an earlier one: `import tutorial.ch03.Snippets.*`.
Language imports (`import language...`) are moved before the object, after the package clauses. The flags are read from
`scalac-flags.txt` next to this script. Warnings are not failures.

Exits with status 1 if a compiled block fails or a `fails` block compiles.
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))


@dataclass
class Block:
    chapter: str
    line: int  # line of the opening fence, 1-based
    code: list
    unit: str = "Snippets"
    fails: bool = False
    sketch: bool = False
    library: bool = False


@dataclass
class Unit:
    chapter: str
    name: str
    blocks: list = field(default_factory=list)

    @property
    def library(self):
        return any(b.library for b in self.blocks)


def chapter_of(heading):
    m = re.match(r"## Chapter (\d+)\.", heading)
    if m:
        return "ch%02d" % int(m.group(1))
    m = re.match(r"## Appendix ([A-Z])\.", heading)
    if m:
        return "app" + m.group(1).lower()
    if heading.startswith("## Preface"):
        return "preface"
    return None


def parse(path):
    blocks = []
    chapter = "preface"
    lines = open(path, encoding="utf-8").read().split("\n")
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("## "):
            chapter = chapter_of(line) or chapter
        fence = re.match(r"^(\s*)```scala\b(.*)$", line)
        if fence:
            indent, info = fence.group(1), fence.group(2).split()
            start = i + 1
            code = []
            i += 1
            while i < len(lines) and not re.match(r"^\s*```\s*$", lines[i]):
                text = lines[i]
                code.append(text[len(indent):] if text.startswith(indent) else text.lstrip())
                i += 1
            block = Block(chapter, start, code)
            for token in info:
                if token.startswith("unit="):
                    block.unit = token[len("unit="):]
                elif token == "fails":
                    block.fails = True
                elif token == "sketch":
                    block.sketch = True
                elif token == "library":
                    block.library = True
                else:
                    raise SystemExit(f"{path}:{start}: unknown snippet option '{token}'")
            blocks.append(block)
        elif re.match(r"^\s*```", line):
            # skip other fenced blocks entirely
            i += 1
            while i < len(lines) and not re.match(r"^\s*```\s*$", lines[i]):
                i += 1
        i += 1
    return blocks


def render(chapter, unit_name, blocks):
    """Returns the source of one compilation unit and, per source line, the document line it comes from."""
    header, body, origins_header, origins_body = [], [], [], []
    for b in blocks:
        for offset, text in enumerate(b.code):
            if re.match(r"^\s*import\s+(scala\.)?language\.", text):
                header.append(text.strip())
                origins_header.append(b.line + 1 + offset)
            elif text.startswith("//>"):
                continue
            else:
                body.append("  " + text)
                origins_body.append(b.line + 1 + offset)
        body.append("")
        origins_body.append(None)
    pkg = ["package tutorial", f"package {chapter}", ""]
    source = pkg + header + [""] + [f"object {unit_name} {{"] + body + ["}"]
    origins = [None] * len(pkg) + origins_header + [None] + [None] + origins_body + [None]
    return "\n".join(source) + "\n", origins


def compile_unit(source, origins, out, classpath, flags, document):
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "Snippet.scala")
        with open(path, "w", encoding="utf-8") as f:
            f.write(source)
        cmd = ["scalac"] + flags + ["-color:never", "-d", out]
        if classpath:
            cmd += ["-classpath", classpath]
        cmd.append(path)
        result = subprocess.run(cmd, capture_output=True, text=True)
        output = result.stdout + result.stderr

        def relocate(m):
            line = int(m.group(1))
            origin = origins[line - 1] if 0 < line <= len(origins) else None
            where = f"{document}:{origin}" if origin else f"(generated line {line})"
            return where

        output = re.sub(r"\S*Snippet\.scala:(\d+)(:\d+)?", relocate, output)
        return result.returncode == 0, output


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--document", default=os.path.join(ROOT, "docs", "TUTORIAL.md"))
    parser.add_argument("--classpath", default="", help="classpath of the compiled library, for `library` units")
    parser.add_argument("--only", default="", help="comma-separated chapters to check, e.g. ch02,ch03,appa")
    parser.add_argument("--keep", default="", help="directory for the compiled snippets (default: a temporary one)")
    parser.add_argument("--verbose", action="store_true", help="print why each `fails` block fails")
    args = parser.parse_args()

    flags = open(os.path.join(HERE, "scalac-flags.txt"), encoding="utf-8").read().split()
    document = os.path.relpath(args.document, os.getcwd())
    only = set(filter(None, args.only.split(",")))
    blocks = [b for b in parse(args.document) if not only or b.chapter in only]

    units, order = {}, []
    for b in blocks:
        if b.sketch:
            continue
        key = (b.chapter, b.unit)
        if key not in units:
            units[key] = Unit(b.chapter, b.unit)
            order.append(key)
        units[key].blocks.append(b)

    out = args.keep or tempfile.mkdtemp(prefix="snippets-")
    os.makedirs(out, exist_ok=True)
    failures, checked, expected_failures, sketches = [], 0, 0, sum(1 for b in blocks if b.sketch)

    for key in order:
        unit = units[key]
        classpath = os.pathsep.join(filter(None, [out, args.classpath if unit.library else ""]))
        compiled = [b for b in unit.blocks if not b.fails]
        source, origins = render(unit.chapter, unit.name, compiled)
        ok, output = compile_unit(source, origins, out, classpath, flags, document)
        checked += len(compiled)
        print(f"{unit.chapter} {unit.name}: {len(compiled)} block(s) {'ok' if ok else 'FAILED'}")
        if not ok:
            failures.append((unit, output))
        for i, b in enumerate(unit.blocks):
            if not b.fails:
                continue
            expected_failures += 1
            prefix = [p for p in unit.blocks[:i] if not p.fails]
            with tempfile.TemporaryDirectory() as scratch:
                source, origins = render(unit.chapter, unit.name, prefix + [b])
                ok, output = compile_unit(source, origins, scratch, classpath, flags, document)
            if ok:
                failures.append((unit, f"{document}:{b.line}: block marked `fails` compiles\n"))
                print(f"{unit.chapter} {unit.name}: `fails` block at line {b.line} COMPILES")
            else:
                print(f"{unit.chapter} {unit.name}: `fails` block at line {b.line} fails as expected")
                if args.verbose:
                    print("    " + "\n    ".join(line for line in output.splitlines() if line.strip()))

    for unit, output in failures:
        print(f"\n==== {unit.chapter} {unit.name} ====\n{output}")
    print(
        f"\nSummary: {checked} compiled block(s) in {len(order)} unit(s), {expected_failures} `fails` block(s), "
        f"{sketches} sketch(es) skipped, {len(failures)} failure(s)."
    )
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
