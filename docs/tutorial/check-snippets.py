#!/usr/bin/env python3
"""Compiles the Scala code blocks of the tutorial, so that every snippet is checked by the compiler.

Usage:
    docs/tutorial/check-snippets.py [--document FILE]... [--classpath CP] [--only ch02,ch03,...] [--keep DIR]
                                    [--verbose]

Without `--document`, the tutorial is checked, then the solutions of its exercises (`exercises/SOLUTIONS.md`) and the
README of the repository. The units of the tutorial are in the package `tutorial`. Every other document has a package
named after its file (`solutions`, `readme`), may import the units of the documents before it, and is compiled against
the library whether its blocks say `library` or not.

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
Language imports (`import language...`) are moved before the object, after the package clauses. Every unit is compiled
by Scala CLI (`scala` on the PATH) with the Scala version of the library, SCALA_VERSION, whatever `scalac` the system
has. The flags are read from `scalac-flags.txt` next to this script: each must be a compiler option of `build.sbt`, and
the preface of the tutorial must list exactly them, or the checker stops before compiling. Warnings are not failures.

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

# The Scala version of the library (`build.sbt`): a compiler can only read the classes of its own or older versions.
SCALA_VERSION = "3.10.0"


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


def render(root, chapter, unit_name, blocks):
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
    pkg = [f"package {root}", f"package {chapter}", ""]
    source = pkg + header + [""] + [f"object {unit_name} {{"] + body + ["}"]
    origins = [None] * len(pkg) + origins_header + [None] + [None] + origins_body + [None]
    return "\n".join(source) + "\n", origins


def compile_unit(source, origins, out, classpath, flags, document):
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "Snippet.scala")
        with open(path, "w", encoding="utf-8") as f:
            f.write(source)
        cmd = ["scala", "compile", "--server=false", "-S", SCALA_VERSION, "--compilation-output", out]
        for flag in flags + ["-color:never"]:
            cmd += ["-O", flag]
        if classpath:
            cmd += ["--classpath", classpath]
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


def check(path, root, library, args, flags, out):
    """Compiles the blocks of the document at `path` into `out`; returns its failures and its counts."""
    document = os.path.relpath(path, os.getcwd())
    only = set(filter(None, args.only.split(",")))
    blocks = [b for b in parse(path) if not only or b.chapter in only]

    units, order = {}, []
    for b in blocks:
        if b.sketch:
            continue
        key = (b.chapter, b.unit)
        if key not in units:
            units[key] = Unit(b.chapter, b.unit)
            order.append(key)
        units[key].blocks.append(b)

    failures, checked, expected_failures, sketches = [], 0, 0, sum(1 for b in blocks if b.sketch)

    for key in order:
        unit = units[key]
        classpath = os.pathsep.join(filter(None, [out, args.classpath if unit.library or library else ""]))
        compiled = [b for b in unit.blocks if not b.fails]
        source, origins = render(root, unit.chapter, unit.name, compiled)
        ok, output = compile_unit(source, origins, out, classpath, flags, document)
        checked += len(compiled)
        print(f"{root} {unit.chapter} {unit.name}: {len(compiled)} block(s) {'ok' if ok else 'FAILED'}")
        if not ok:
            failures.append((unit, output))
        for i, b in enumerate(unit.blocks):
            if not b.fails:
                continue
            expected_failures += 1
            prefix = [p for p in unit.blocks[:i] if not p.fails]
            with tempfile.TemporaryDirectory() as scratch:
                source, origins = render(root, unit.chapter, unit.name, prefix + [b])
                ok, output = compile_unit(source, origins, scratch, classpath, flags, document)
            if ok:
                failures.append((unit, f"{document}:{b.line}: block marked `fails` compiles\n"))
                print(f"{root} {unit.chapter} {unit.name}: `fails` block at line {b.line} COMPILES")
            else:
                print(f"{root} {unit.chapter} {unit.name}: `fails` block at line {b.line} fails as expected")
                if args.verbose:
                    print("    " + "\n    ".join(line for line in output.splitlines() if line.strip()))
    return failures, checked, len(order), expected_failures, sketches


def check_flags(flags, tutorial):
    """The flags of the checker must be flags of the build, and the preface of the tutorial must list exactly them."""
    problems = []
    build = set(re.findall(r'^\s*"(-[^"]+)",', open(os.path.join(ROOT, "build.sbt"), encoding="utf-8").read(), re.M))
    for flag in flags:
        if flag not in build:
            problems.append(f"scalac-flags.txt: {flag} is not a compiler option of build.sbt")
    text = open(tutorial, encoding="utf-8").read()
    listed = re.search(r"with the following compiler options:\n\n```\n(.*?)\n```", text, re.S)
    if not listed:
        problems.append("TUTORIAL.md: the preface does not list the compiler options")
    elif sorted(listed.group(1).split()) != sorted(flags):
        problems.append("TUTORIAL.md: the compiler options of the preface are not those of scalac-flags.txt")
    return problems


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--document", action="append", default=[], help="a document to check; may be repeated")
    parser.add_argument("--classpath", default="", help="classpath of the compiled library, for `library` units")
    parser.add_argument("--only", default="", help="comma-separated chapters to check, e.g. ch02,ch03,appa")
    parser.add_argument("--keep", default="", help="directory for the compiled snippets (default: a temporary one)")
    parser.add_argument("--verbose", action="store_true", help="print why each `fails` block fails")
    args = parser.parse_args()

    flags = open(os.path.join(HERE, "scalac-flags.txt"), encoding="utf-8").read().split()
    tutorial = os.path.join(ROOT, "docs", "TUTORIAL.md")
    documents = args.document or [
        tutorial,
        os.path.join(HERE, "exercises", "SOLUTIONS.md"),
        os.path.join(ROOT, "README.md"),
    ]
    problems = check_flags(flags, tutorial)
    if problems:
        sys.exit("\n".join(problems))
    out = args.keep or tempfile.mkdtemp(prefix="snippets-")
    os.makedirs(out, exist_ok=True)

    failures, checked, units, expected_failures, sketches = [], 0, 0, 0, 0
    for path in documents:
        is_tutorial = os.path.abspath(path) == tutorial
        root = "tutorial" if is_tutorial else re.sub(r"\W", "", os.path.splitext(os.path.basename(path))[0]).lower()
        result = check(path, root, not is_tutorial, args, flags, out)
        failures += result[0]
        checked, units = checked + result[1], units + result[2]
        expected_failures, sketches = expected_failures + result[3], sketches + result[4]

    for unit, output in failures:
        print(f"\n==== {unit.chapter} {unit.name} ====\n{output}")
    print(
        f"\nSummary: {checked} compiled block(s) in {units} unit(s), {expected_failures} `fails` block(s), "
        f"{sketches} sketch(es) skipped, {len(failures)} failure(s)."
    )
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
