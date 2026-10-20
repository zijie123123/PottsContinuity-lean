# Vendored: schoenflies-lean (Jordan–Schoenflies theorem)

The planar topology of the proof uses the Jordan curve theorem and the Jordan–Schoenflies theorem
(every homeomorphism between two Jordan curves in the plane extends to a homeomorphism of the
plane), together with the polygonal and graph-theoretic results that their proof develops. The
128 modules of <https://github.com/alonamaloh/schoenflies-lean> that these uses need (the import
closure of the modules imported by `PottsContinuity/`) are vendored here.

- Upstream repository: https://github.com/alonamaloh/schoenflies-lean
- Upstream commit: `05a43d29cde026618777db3d4e4316204ccca237`
- Licence: Apache-2.0 — see `LICENSE` in this directory; the source files carry the notice
  "Copyright (c) 2026 Álvaro Begué". The licence of this repository is also Apache-2.0.
- Files: `Schoenflies/**.lean`, 128 modules; the upstream `Challenge`/`Solution` modules and
  unused modules are not included.

Changes relative to the upstream commit (no change to any statement apart from the rename of
`Graph.IsBridge` described below):

1. the compatibility edits of openai/math's patch for Lean v4.34.1 (see below) and the Mathlib commit used during development
   (`d13f23b723b8a846827a245b89c10fc7d3f11612`): renamed or deprecated Mathlib names
   (e.g. `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, `dif_pos` → `dite_eq_left`) and
   `letI`/`haveI` → `let`/`have` where the linter asks for it (upstream targets Lean v4.32.2);
2. a mechanical port to the Lean module system (`module`, `public import`,
   `@[expose] public section`), required because every Lean file in a Palomar submission must be a
   module, and one `private def` (`farSide` in `Schoenflies/PrePolygonSep.lean`) made public;
3. four proofs (five places) that unfolded Mathlib's `Graph.deleteVerts`, whose body is not exposed to importing
   modules under the module system, now use Mathlib's `Graph.vertexSet_deleteVerts` and
   `Graph.deleteVerts_isLink` instead (`Schoenflies/Graph/TwoConnected.lean`,
   `Schoenflies/Graph/Tree.lean`, `Schoenflies/Graph/Relabel.lean`, `Schoenflies/InitialPair.lean`).

The move from Lean v4.34.1 to Lean v4.35.0-rc3 / Mathlib v4.35.0-rc3 required no further change.

The library is built with the options of the upstream lakefile (`relaxedAutoImplicit = false`,
`maxSynthPendingDepth = 3`; `autoImplicit` left at its default, `true`), set for the
`Schoenflies` library in this repository's `lakefile.toml`.

The Lean v4.34.1 compatibility edits (item 1) are exactly those of
`lean/patches/schoenflies-lean-lean4341.patch` of <https://github.com/openai/math> at commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (SHA-256 `4cbc255a2be785e6b617ecd61cdaf67e6d236d65a87f284380f2713670c8e350`), which is licensed under the Apache License 2.0; this includes
the docstrings that patch rewrites and the rename of `Graph.IsBridge` and its lemmas to `Graph.IsSchoenfliesBridge`, the only change to a statement.
