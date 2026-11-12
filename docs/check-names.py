#!/usr/bin/env python3
"""Checks that the qualified names the documents mention exist in the code.

Usage, from the repository root:
    python3 docs/check-names.py

Every backticked `Name.member` in CLAUDE.md, README.md and the documents of `docs/` is resolved against the
declarations of `src/main` and `src/test`: the first name must be declared somewhere, a nested type or object must be
declared in a file that declares its owner or one of the classes its owner extends, and a member in lower case must be
declared somewhere (it may be inherited). This is a check by names, not by symbols: it finds a renamed or removed structure, not a changed
signature. Names of other libraries and of the tutorial's own snippets are in ALLOWED. Exits with status 1 and lists
the names it cannot resolve.
"""

import collections
import glob
import re
import sys

DOCUMENTS = ["CLAUDE.md", "README.md", "docs/DESIGN.md", "docs/CONCEPTS.md", "docs/TUTORIAL.md",
             "docs/compiler-issues.md", "docs/tutorial/README.md", "docs/tutorial/exercises/SOLUTIONS.md"]

# First names that are not the library's: the standard library, the build, test libraries, and names that the
# tutorial declares in its own snippets or uses as examples.
ALLOWED = set("""
    Gen Test Def Files Paths List Option Some None Either Left Right Vector Set Map Int Long String Boolean Unit
    Nothing Double BigInt Char Array Tuple Tuple2 Try Success Failure Console System Math Predef Seq Iterator
    LazyList Function1 CanEqual Ordering Numeric Regex Cogen Arbitrary Prop Type TypeRepr Expr Quotes Any Function
    K V O Cat OptionMap
""".split())

# Mentions of files are not names of the code.
FILES = (".md", ".scala", ".py", ".sbt", ".txt", ".toml", ".json")

DECLARATION = re.compile(
    r"^\s*(?:(?:final|sealed|private(?:\[\w+\])?|protected|override|open|abstract|inline|lazy|implicit|tracked|case|"
    r"opaque|transparent|infix)\s+)*(class|object|trait|enum|type|def|val|var|given|case)\s+`?([A-Za-z_]\w*)"
)
MENTION = re.compile(r"`([A-Z]\w*(?:\.[A-Za-z_]\w*)+)")


def declarations():
    by_file, files_of = {}, collections.defaultdict(set)
    for path in glob.glob("src/**/*.scala", recursive=True):
        names = set()
        for line in open(path, encoding="utf-8"):
            match = DECLARATION.match(line)
            if match:
                names.add(match.group(2))
            for parameter in re.findall(r"(?:val|tracked val)\s+(\w+)\s*:", line):
                names.add(parameter)
        by_file[path] = names
        for name in names:
            files_of[name].add(path)
    parents = {
        path: set(re.findall(r"extends\s+(?:[a-z]\w*\.)*([A-Z]\w*)", open(path, encoding="utf-8").read()))
        for path in by_file
    }
    return by_file, files_of, parents


def with_parents(owners, files_of, parents):
    """The files `owners` and, three levels up, the files that declare what their classes extend."""
    result = set(owners)
    for _ in range(3):
        result |= {f for owner in set(result) for parent in parents[owner] for f in files_of.get(parent, ())}
    return result


def resolve(path, by_file, files_of, parents):
    """Returns the first segment of `path` that cannot be resolved, or None."""
    first, rest = path[0], path[1:]
    if first in ALLOWED:
        return None
    if first not in files_of:
        return first
    owners = files_of[first]
    for segment in rest:
        if segment in ("type", "this", "apply"):
            continue
        if segment[0].isupper():
            nested = {f for f in with_parents(owners, files_of, parents) if segment in by_file[f]}
            if not nested:
                return segment
            owners = files_of[segment]
        elif segment not in files_of:
            return segment
        else:
            owners = owners | files_of[segment]
    return None


def main():
    by_file, files_of, parents = declarations()
    unresolved = []
    for document in DOCUMENTS:
        try:
            lines = open(document, encoding="utf-8").read().split("\n")
        except FileNotFoundError:
            continue
        fenced = False
        for number, line in enumerate(lines, 1):
            if line.lstrip().startswith("```"):
                fenced = not fenced
                continue
            if fenced:
                continue
            for mention in MENTION.findall(line):
                if mention.endswith(FILES):
                    continue
                missing = resolve(mention.split("."), by_file, files_of, parents)
                if missing:
                    unresolved.append(f"{document}:{number}: `{mention}`: no declaration of {missing}")
    for line in unresolved:
        print(line)
    print(f"{len(unresolved)} name(s) without a declaration.")
    sys.exit(1 if unresolved else 0)


if __name__ == "__main__":
    main()
