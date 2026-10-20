module

public import PottsContinuity.Infinite.ComparisonStatements
public import PottsContinuity.PD.RCInfinite.CylinderApproximation
public import PottsContinuity.PD.RCInfinite.ErgodicLimits
public import PottsContinuity.PD.RCInfinite.SubgraphExhaustion
public import PottsContinuity.PD.RCInfinite.BurtonKeane
public import PottsContinuity.PD.RCInfinite.PercolationZeroOne
public import PottsContinuity.WellDefined.Uniqueness
public import PottsContinuity.Infinite.Bridge

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Coincidence

open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

/-- At a parameter above the genuine critical point, any coincident free and
wired limits have an infinite cluster almost surely and at most one infinite
cluster almost surely. -/
theorem coincident_free_limit_unique_infinite_cluster
    (q : Set.Ici (1 : ℝ)) (pc : ℝ) (hpc : IsRCCriticalPoint q pc)
    (t : Set.Icc (0 : ℝ) 1) (hpt : pc < (t : ℝ))
    (hpt0 : 0 < (t : ℝ)) (hpt1 : (t : ℝ) < 1)
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit t
      ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one q.2)⟩ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit t
      ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one q.2)⟩ 1 μ₁)
    (hEq : μ₀ = μ₁) :
    ∀ᵐ ω ∂μ₀, atMostOneInfiniteCluster ω ∧ ω ∈ infiniteClusterEvent := by
  let : IsProbabilityMeasure μ₀ := hμ₀.1
  let q' : Set.Ioi (0 : ℝ) :=
    ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one q.2)⟩
  obtain ⟨μc, hμc, _, hpercolates⟩ := hpc.2 t
  have hμcEq : μc = μ₁ :=
    PottsContinuity.WellDefined.limit_unique t q' 1 μc μ₁ hμc hμ₁
  have hpos₁ : 0 < μ₁ (infiniteAt (0, 0)) := by
    rw [← hμcEq]
    exact hpercolates hpt
  have hpos₀ : 0 < μ₀ (infiniteAt (0, 0)) := by
    rw [hEq]
    exact hpos₁
  let θ := Infinite.pdParameters t q' hpt0 hpt1 q.2
  have hμ₀PD : PottsContinuity.PD.IsRCInfiniteVolumeLimit t q' 0 μ₀ :=
    Infinite.isRCInfiniteVolumeLimit_to_PD_box t q' 0 μ₀ hμ₀
  have hμ₀PDθ : PottsContinuity.PD.IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀ := by
    rw [Infinite.pdParameters_toP t q' hpt0 hpt1 q.2,
      Infinite.pdParameters_toQ t q' hpt0 hpt1 q.2]
    exact hμ₀PD
  have hcluster : μ₀ infiniteClusterEvent = 1 :=
    (infiniteCluster_eq_one_iff_origin_pos t q' q.2 0 μ₀ hμ₀PD).mpr hpos₀
  have hclusterNull : μ₀ infiniteClusterEventᶜ = 0 := by
    have hcompl := measure_compl (μ := μ₀) measurableSet_infiniteClusterEvent
    rw [measure_univ, hcluster] at hcompl
    simpa using hcompl
  have hevent : ∀ᵐ ω ∂μ₀, ω ∈ infiniteClusterEvent := ae_iff.mpr hclusterNull
  have hunique : ∀ᵐ ω ∂μ₀, atMostOneInfiniteCluster ω :=
    isRCInfiniteVolumeLimit_atMostOneInfiniteCluster θ 0 μ₀ hμ₀PDθ
  filter_upwards [hunique, hevent] with ω hω₁ hω₂
  exact ⟨hω₁, hω₂⟩

end

end PottsContinuity.Coincidence
