-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripClosedCutFailureDecay.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutFailure
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial

noncomputable section

/-- For fixed strip height and a fixed initial collar, either closed-cut scan
failure vanishes as the rectangle grows, uniformly over arbitrary outer
boundary conditions. -/
theorem tendsto_horizontalStripEitherBlockScan_none_probability_zero
    (q : PottsContinuity.FKC.ClusterWeight) (n K : ℕ)
    (ξ : (N : ℕ) → PottsContinuity.FKC.FiniteFK.BoundaryCondition
      (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n))) :
    Tendsto
      (fun N => (PottsContinuity.FKC.FiniteFK.measure
        (horizontalStripCutRectangle N n) q (ξ N)
        {A | (horizontalStripLeftBlockScan N n K A).2 = none ∨
          (horizontalStripRightBlockScan N n K A).2 = none}).toReal)
      atTop (𝓝 0) := by
  let κ : ℝ := 1 / (1 + PottsContinuity.FKC.loopWeight q)
  let ρ : ℝ := 1 - κ ^ (2 * n + 1)
  have hκpos : 0 < κ := by
    dsimp [κ]
    exact div_pos (by norm_num) (PottsContinuity.FKC.one_add_loopWeight_pos q)
  have hκnonneg : 0 ≤ κ := hκpos.le
  have hκle : κ ≤ 1 := by
    dsimp [κ]
    rw [div_le_one (PottsContinuity.FKC.one_add_loopWeight_pos q)]
    linarith [PottsContinuity.FKC.one_le_loopWeight q]
  have hκpow : κ ^ (2 * n + 1) ≤ 1 := pow_le_one₀ hκnonneg hκle
  have hρnonneg : 0 ≤ ρ := by
    dsimp [ρ]
    linarith
  have hρlt : ρ < 1 := by
    have hpowpos : 0 < κ ^ (2 * n + 1) := pow_pos hκpos _
    dsimp [ρ]
    linarith
  have hpow : Tendsto (fun m : ℕ => ρ ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρnonneg hρlt
  apply (Metric.tendsto_nhds).2
  intro ε hε
  have hpow_eventually : ∀ᶠ m : ℕ in atTop, ρ ^ m < ε / 2 := by
    have hball := (Metric.tendsto_nhds.1 hpow) (ε / 2) (by linarith)
    filter_upwards [hball] with m hm
    simpa [Real.dist_eq, abs_of_nonneg hρnonneg] using hm
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hpow_eventually
  refine Filter.eventually_atTop.2 ⟨K + M, ?_⟩
  intro N hN
  have hKN : K ≤ N := by omega
  have hMN : M ≤ N - K := by omega
  have hbound := horizontalStripEitherBlockScan_none_probability_le
    q N n K hKN (ξ N)
  have hpower : ρ ^ (N - K) ≤ ρ ^ M :=
    pow_le_pow_of_le_one hρnonneg hρlt.le hMN
  have hupper :
      (PottsContinuity.FKC.FiniteFK.measure (horizontalStripCutRectangle N n) q (ξ N)
        {A | (horizontalStripLeftBlockScan N n K A).2 = none ∨
          (horizontalStripRightBlockScan N n K A).2 = none}).toReal ≤
        2 * ρ ^ M := by
    calc
      _ ≤ 2 * ρ ^ (N - K) := by simpa [κ, ρ] using hbound
      _ ≤ 2 * ρ ^ M := mul_le_mul_of_nonneg_left hpower (by norm_num)
  have hsmall : 2 * ρ ^ M < ε := by
    have hMε := hM M le_rfl
    linarith
  have hnonneg : 0 ≤
      (PottsContinuity.FKC.FiniteFK.measure (horizontalStripCutRectangle N n) q (ξ N)
        {A | (horizontalStripLeftBlockScan N n K A).2 = none ∨
          (horizontalStripRightBlockScan N n K A).2 = none}).toReal :=
    ENNReal.toReal_nonneg
  simpa [Real.dist_eq, abs_of_nonneg hnonneg] using lt_of_le_of_lt hupper hsmall

end
end PottsContinuity.FKC.Medial
