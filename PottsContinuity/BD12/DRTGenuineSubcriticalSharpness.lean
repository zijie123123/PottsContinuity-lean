module

public import PottsContinuity.BD12.DRTWiredZeroLimit
public import PottsContinuity.BD12.DRTWiredSharpnessFromZero
public import PottsContinuity.Frozen.Defs

/-! Exponential decay of the actual finite wired one-arm sequence throughout
the subcritical interval of the frozen genuine threshold. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory Filter
open scoped Topology

/-- Actual finite wired exponential decay below any genuine critical point.
The parameter is the homogeneous physical probability 1-exp(-beta). -/
theorem drt_genuine_subcritical_exponential_decay
    (q : Set.Ici (1 : ℝ)) (pc : ℝ) (hpc : IsRCCriticalPoint q pc)
    (β : Set.Ioi (0 : ℝ)) (hβ : 1 - Real.exp (-(β : ℝ)) < pc) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      drtWiredOneArmMean ⟨(q : ℝ), (show (0 : ℝ) < (q : ℝ) from lt_of_lt_of_le one_pos q.property)⟩ β n ≤ Real.exp (-c * n) := by
  have hcont : ContinuousAt (fun t : ℝ => 1 - Real.exp (-t)) (β : ℝ) :=
    (continuous_const.sub (Real.continuous_exp.comp continuous_neg)).continuousAt
  have hev0 : ∀ᶠ t : ℝ in 𝓝 (β : ℝ), 1 - Real.exp (-t) < pc := hcont (gt_mem_nhds hβ)
  have hev : ∀ᶠ t : ℝ in 𝓝[>] (β : ℝ), 1 - Real.exp (-t) < pc :=
    hev0.filter_mono nhdsWithin_le_nhds
  obtain ⟨d,hdp,hβd⟩ := (hev.and self_mem_nhdsWithin).exists
  let δ : Set.Ioi (0 : ℝ) := ⟨d,β.property.trans hβd⟩
  let q' : Set.Ioi (0 : ℝ) := ⟨(q : ℝ), (show (0 : ℝ) < (q : ℝ) from lt_of_lt_of_le one_pos q.property)⟩
  let θ := drtHomogeneousParameters q' q.property δ
  obtain ⟨μ,hμ,hzero,_⟩ := hpc.2 θ.toP
  have hμ' : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ := hμ
  have hz := drtWiredOneArmMean_tendsto_zero_of_wired_nonpercolation q' q.property δ μ hμ' (hzero hdp)
  exact drt_wired_exponential_decay_of_oneArmZero q' q.property β δ hβd hz

end PottsContinuity.BD12
