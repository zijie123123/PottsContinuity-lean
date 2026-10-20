-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Frozen/Defs/RCCriticalParameter.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Tactic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# `rcCriticalParameter` from the PottsDiscontinuity formalization

A definition of the formalization of arXiv:1611.09877v2 that is reused here by the adapted
modules of `PottsContinuity/PD/`. It is not part of the statement surface of this repository.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsContinuity.PD

/-- `p_c(q) = √q / (1 + √q)` for `q ≥ 1`, as an element of `[0, 1]`: the value of the critical
parameter stated on p. 4 (identified in [3]); criticality itself is not asserted here. -/
noncomputable def rcCriticalParameter (q : Set.Ici (1 : ℝ)) : Set.Icc (0 : ℝ) 1 :=
  ⟨Real.sqrt q / (1 + Real.sqrt q),
    div_nonneg (Real.sqrt_nonneg _) (by positivity),
    (div_le_one (by positivity)).2 (by linarith)⟩

end PottsContinuity.PD
