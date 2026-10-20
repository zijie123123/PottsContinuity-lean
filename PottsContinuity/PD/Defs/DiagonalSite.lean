-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Frozen/Defs/DiagonalSite.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Tactic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# `diagonalSite` from the PottsDiscontinuity formalization

A definition of the formalization of arXiv:1611.09877v2 that is reused here by the adapted
modules of `PottsContinuity/PD/`. It is not part of the statement surface of this repository.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsContinuity.PD

/-- `xₙ`: the site of `ℤ²` with both coordinates equal to `⌊n/2⌋`. -/
def diagonalSite (n : ℕ) : ℤ × ℤ :=
  (((n / 2 : ℕ) : ℤ), ((n / 2 : ℕ) : ℤ))

end PottsContinuity.PD
