#!/usr/bin/env python3
"""Checks that every law has a row in the law status table.

Usage, from the repository root, after `sbt --client testFull` has regenerated the table:
    python3 docs/check-laws.py

A law is a `def` directly inside an `object <Name>Laws` of `src/main`, or inside its nested `object Consequences`.
It has a row if `docs/law-status.md` has a row with its name in any section: a refinement's laws are reported under
the structure whose spec runs them. Exits with status 1 and lists the laws without a row.

Exempt, each for the reason CLAUDE.md gives:
    IsoLaws                                 checked through PremonoidalLaws and ModuleLaws
    PremonoidalLaws.interchangeLeft/Right   premises of the centrality laws, which call them
"""

import collections
import glob
import re
import sys

EXEMPT = {("Iso", "leftInverse"), ("Iso", "rightInverse"), ("Premonoidal", "interchangeLeft"),
          ("Premonoidal", "interchangeRight")}


def laws():
    found = collections.defaultdict(set)
    for path in sorted(glob.glob("src/main/scala/parrot/**/*.scala", recursive=True)):
        current, indent, nested = None, 0, None
        for line in open(path, encoding="utf-8"):
            depth = len(line) - len(line.lstrip())
            opening = re.match(r"\s*object (\w+)Laws\b", line)
            if opening and current is None:
                current, indent, nested = opening.group(1), depth, None
                continue
            if current is None:
                continue
            if line.strip() == "}" and depth == indent:
                current = None
            elif re.match(r"\s*object Consequences\b", line) and depth == indent + 2:
                nested = depth
            elif line.strip() == "}" and nested is not None and depth == nested:
                nested = None
            else:
                member = re.match(r"\s*def (\w+)", line)
                if member and depth == (nested if nested is not None else indent) + 2:
                    found[current].add(member.group(1))
    return found


def rows():
    names = set()
    for line in open("docs/law-status.md", encoding="utf-8"):
        cells = [cell.strip() for cell in line.split("|")]
        if len(cells) > 4 and cells[1] not in ("Law", "---", "Status"):
            names.add(cells[1])
    return names


def main():
    tested = rows()
    missing = [
        f"{structure}Laws.{law}"
        for structure, names in sorted(laws().items())
        for law in sorted(names)
        if law not in tested and (structure, law) not in EXEMPT
    ]
    for law in missing:
        print(f"no row in docs/law-status.md: {law}")
    print(f"{len(missing)} law(s) without a row.")
    sys.exit(1 if missing else 0)


if __name__ == "__main__":
    main()
