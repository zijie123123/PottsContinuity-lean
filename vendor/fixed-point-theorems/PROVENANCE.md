# Vendored: fixed-point-theorems (Brouwer's fixed-point theorem)

The proof uses Brouwer's fixed-point theorem (`brouwer_fixed_point`). It is applied in
`PottsContinuity/PD/Duality/RectanglePathIntersection.lean` and
`PottsContinuity/FKC/Curves/RectanglePathIntersection.lean` to show that two crossing paths of a
rectangle intersect. Mathlib (commit `b63f6e8`, toolchain v4.35.0-rc3) does not contain this
theorem, so the five modules of <https://github.com/harfe/fixed-point-theorems-lean4> that prove it
are vendored here.

- Upstream repository: https://github.com/harfe/fixed-point-theorems-lean4
- Upstream commit: `770940ddf9878cf61952ed53d910b92bca841838`
- Licence: MIT, copyright (c) 2026 harfe — see `LICENSE` in this directory. The licence of this
  repository (Apache-2.0) does not apply to the upstream code; the compatibility edits come from
  openai/math under Apache-2.0 (see below).
- Files: `FixedPointTheorems/{brouwer,apply_cubical_sperner,convex_homeos,cubical_sperner,cubical_sperner_prep}.lean`
  (the upstream `kakutani.lean` is not used and not included).

Changes relative to the upstream commit (no change to any statement); the files are byte-identical
to the vendored copy in https://github.com/zijie123123/PottsDiscontinuity-lean:

1. compatibility edits for recent Lean and Mathlib (deprecated names, `import Mathlib`, proof
   repairs), first for Lean v4.34.1 by openai/math's patch (see below) and then for Lean v4.35.0-rc3 / Mathlib v4.35.0-rc3
   (the later move to Mathlib commit `b63f6e8` required no further change);
2. a mechanical port to the Lean module system (`module`, `public import`,
   `@[expose] public section`), required because every Lean file in a Palomar submission must be a
   module.

The Lean v4.34.1 compatibility edits (item 1) are exactly those of
`lean/patches/fixed-point-theorems-lean4341.patch` of <https://github.com/openai/math> at commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (SHA-256 `d70872e41e80b25191538d1659c4aa3a001349b5bd16f806c9e3833a502516e5`), which is licensed under the Apache License 2.0; this includes
the docstrings that patch rewrites. The patch content is Apache-2.0; the upstream files remain MIT.
