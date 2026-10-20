module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.Provider.IsPottsInfiniteVolumeLimitUnique

/-!
# Theorem `isPottsInfiniteVolumeLimit_unique`

Well-definedness of the infinite-volume Potts measures `μ^{(i)}_β` (p. 4), which is implicit in the
notation of H. Duminil-Copin, V. Sidoravicius and V. Tassion, arXiv:1505.04159v1; it makes the
existential form of the main theorems determine the paper's objects. The statement was approved by
the author before any proof was written; `Challenge.lean` contains it verbatim. The proof is
assembled in `PottsContinuity.Provider.isPottsInfiniteVolumeLimit_unique`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PottsContinuity

/-- Well-definedness of `μ^{(i)}_{ℤ²,β}`: the infinite-volume limit is unique. -/
theorem isPottsInfiniteVolumeLimit_unique (q : ℕ) (β : ℝ) (i : Fin q) (μ ν : Measure (ℤ × ℤ → Fin q))
    (hμ : IsPottsInfiniteVolumeLimit q β i μ) (hν : IsPottsInfiniteVolumeLimit q β i ν) : μ = ν :=
  by exact PottsContinuity.Provider.isPottsInfiniteVolumeLimit_unique

end PottsContinuity
