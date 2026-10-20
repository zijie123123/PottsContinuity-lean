module

public import PottsContinuity.Frozen.Defs

@[expose] public section

namespace PottsContinuity.Coincidence

open MeasureTheory
open PottsContinuity

/-- Parameters in `(0,1)` at which some free and wired frozen limits differ. -/
def freeWiredDisagreementSet (q : Set.Ici (1 : ℝ)) : Set ℝ :=
  {p | ∃ hp0 : 0 < p, ∃ hp1 : p < 1, ∃ μ₀ μ₁ : Measure (squareLattice.edgeSet → Bool),
    IsRCInfiniteVolumeLimit ⟨p, ⟨le_of_lt ‹0 < p›, le_of_lt ‹p < 1›⟩⟩
      ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one q.2)⟩ 0 μ₀ ∧
    IsRCInfiniteVolumeLimit ⟨p, ⟨le_of_lt ‹0 < p›, le_of_lt ‹p < 1›⟩⟩
      ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one q.2)⟩ 1 μ₁ ∧
    μ₀ ≠ μ₁}

/-- Outside the disagreement set, any specified free and wired limits at that
interior parameter are equal. -/
theorem free_wired_limits_equal_of_not_mem
    (q : Set.Ici (1 : ℝ)) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (μ₀ μ₁ : Measure (squareLattice.edgeSet → Bool))
    (hμ₀ : IsRCInfiniteVolumeLimit ⟨p, ⟨le_of_lt hp0, le_of_lt hp1⟩⟩
      ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one q.2)⟩ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit ⟨p, ⟨le_of_lt hp0, le_of_lt hp1⟩⟩
      ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one q.2)⟩ 1 μ₁)
    (hnot : p ∉ freeWiredDisagreementSet q) : μ₀ = μ₁ := by
  by_contra hneq
  exact hnot ⟨hp0, hp1, μ₀, μ₁, hμ₀, hμ₁, hneq⟩

end PottsContinuity.Coincidence
