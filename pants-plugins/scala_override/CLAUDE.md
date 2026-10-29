# CLAUDE.md — scala_override

Guidance for developers and AI agents working on the in-repo `scala_override` Pants plugin.

---

## 1. What this plugin does

Pants uses fine-grained, file-level dependency inference for Scala powered by Scalameta. In Pants 2.33.1, the internal Scala parser (`ScalaParser.scala` in `pants.backend.scala.dependency_inference`) has several limitations with modern Scala 3 features:

1. **Rejects `tracked` parameters:** Vanilla Pants parses Scala 3 with `dialects.Scala3`, which rejects `tracked val` constructor parameters (part of Scala 3's modularity proposal).
2. **Ignores infix type operators:** `Type.ApplyInfix` discards `_op`, so symbolic infix types like `~>` and `-->` are not tracked as consumed symbols.
3. **Ignores Scala 3 `given` definitions:** Vanilla Pants only handles Scala 2 `val`, `var`, and `def`, completely omitting `Defn.GivenAlias` and `Defn.Given`.
4. **Fails on relative sibling imports:** In files with chained package clauses (`package parrot; package parser`), relative imports like `import category.*` are not qualified against parent package scopes.

The `scala_override` plugin provides an in-repo override of `ScalaParser.scala` fixing all four issues.

---

## 2. How the plugin works

Pants compiles and runs its Scala parser tool as a standalone Java process. The source code of `ScalaParser.scala` is embedded inside the Pants distribution as a package resource and loaded via `pants.util.resources.read_resource`.

In [`register.py`](register.py):
- The plugin monkeypatches `read_resource` in both `pants.util.resources` and `pants.backend.scala.dependency_inference.scala_parser`.
- When Pants requests `("pants.backend.scala.dependency_inference", "ScalaParser.scala")`, `patched_read_resource` intercepts the call and serves the customized [`ScalaParser.scala`](ScalaParser.scala) from this directory instead of upstream Pants' bundled resource.

---

## 3. Registration and installation

The plugin is configured in [`pants.toml`](../../pants.toml):

```toml
[GLOBAL]
pythonpath = ["%(buildroot)s/pants-plugins"]
backend_packages = [
  "scala_override",
  "pants.backend.experimental.scala",
  # ...
]
```

> [!IMPORTANT]
> In-repo plugins must be loaded via `pythonpath` and `backend_packages`.
> Never add in-repo plugins to `[GLOBAL].plugins` — that setting instructs Pants to download a wheel from PyPI via Pex and will fail with a pip resolution error.

---

## 4. File layout

```
pants-plugins/scala_override/
  AGENTS.md                   Pointer to this file
  CLAUDE.md                   This guide
  __init__.py                 Python package marker
  register.py                 Plugin entrypoint (monkeypatches read_resource)
  ScalaParser.original.scala  Verbatim upstream ScalaParser.scala from Pants 2.33.1
  ScalaParser.scala           The active patched parser loaded by Pants
  ScalaParser.scala.diff      Unified diff from ScalaParser.original.scala to ScalaParser.scala
```

Keeping [`ScalaParser.original.scala`](ScalaParser.original.scala) alongside the patched version makes it easy to inspect upstream differences and generate updated diffs cleanly.

---

## 5. Modifications in `ScalaParser.scala`

1. **`dialects.Scala3Future` (lines ~580):**
   Uses `dialects.Scala3Future` for all Scala 3 versions so Scalameta parses modern features including `tracked` parameters and capture checking syntax.
2. **`Type.ApplyInfix` (lines ~150):**
   Extracts `op` as a consumed symbol in `case Type.ApplyInfix(lhs, op, rhs)` rather than ignoring `_op`.
3. **`enclosingScopes` for relative imports (lines ~220–240):**
   Computes enclosing package scopes from `nameParts` and adds qualified variants to `importsByScope` for relative package imports (`import category.*` -> `parrot.category.*`).
4. **`Defn.GivenAlias` and `Defn.Given` (lines ~395–415):**
   Extracts provided names, consumed signature types (`decltpe`), and type-parameter context bounds (`tparams`) for Scala 3 `given` definitions.

---

## 6. How to edit and maintain

Whenever you modify [`ScalaParser.scala`](ScalaParser.scala):

1. **Regenerate the diff:**
   ```sh
   diff -u -p pants-plugins/scala_override/ScalaParser.original.scala pants-plugins/scala_override/ScalaParser.scala > pants-plugins/scala_override/ScalaParser.scala.diff
   ```
2. **Verify diff applicability:**
   Confirm the diff reverses cleanly against the modified file:
   ```sh
   patch --dry-run -R -p1 < pants-plugins/scala_override/ScalaParser.scala.diff
   ```
3. **Test dependency inference and compilation:**
   ```sh
   pants --no-pantsd dependencies ::
   pants --no-pantsd check ::
   pants --no-pantsd test src/test/scala/parrot/category/StrongTest.scala
   ```

