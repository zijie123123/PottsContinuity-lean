module

public import PottsContinuity.PlanarMixed.TiltedHalfHeight.OpenColumnTail

@[expose] public section

namespace PottsContinuity.PlanarMixed.TiltedHalfHeight
open MeasureTheory Filter Topology Thm3.Prop4
noncomputable section

/-- The uniform failure factor is strictly between zero and one. -/
theorem openColumnFailureFactor_bounds (q : Set.Ici (1 : ℝ)) (N : ℕ) :
    0≤1-openColumnCost q N ∧ 1-openColumnCost q N<1 := by
  constructor <;> linarith [openColumnCost_pos q N,openColumnCost_lt_one q N]

/-- A fully open original column occurs strictly to the right almost surely. -/
theorem ae_exists_fullyOpenColumn_right (q : Set.Ici (1 : ℝ)) (N : ℕ) (t : ℝ) :
    ∀ᵐ ω ∂(selfDualTiltedStripMeasure q N t), ∃ x : ℤ, 0<x ∧ FullyOpenColumn N t x ω := by
  let μ := selfDualTiltedStripMeasure q N t
  let E : Set (TiltedConfiguration N t) := {ω | ¬ ∃ x : ℤ, 0<x ∧ FullyOpenColumn N t x ω}
  have hbound (L : ℕ) : μ.real E ≤ (1-openColumnCost q N)^L := by
    apply le_trans (measureReal_mono (μ := μ) (s₂ := {ω | ∀ j<L,
      ¬FullyOpenColumn N t (1+(j:ℤ)) ω}) ?_) (selfDualTiltedStrip_noOpenColumns_le q N t 1 L)
    intro ω hω j _ hj
    exact hω ⟨1+(j:ℤ),by omega,hj⟩
  have hconv : Tendsto (fun L : ℕ => (1-openColumnCost q N)^L) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (openColumnFailureFactor_bounds q N).1
      (openColumnFailureFactor_bounds q N).2
  have hz : μ.real E=0 := le_antisymm
    (ge_of_tendsto hconv (Eventually.of_forall hbound)) ENNReal.toReal_nonneg
  apply ae_iff.mpr
  exact (measureReal_eq_zero_iff (measure_ne_top μ E)).mp hz

/-- A fully open original column occurs strictly to the left almost surely. -/
theorem ae_exists_fullyOpenColumn_left (q : Set.Ici (1 : ℝ)) (N : ℕ) (t : ℝ) :
    ∀ᵐ ω ∂(selfDualTiltedStripMeasure q N t), ∃ x : ℤ, x<0 ∧ FullyOpenColumn N t x ω := by
  let μ := selfDualTiltedStripMeasure q N t
  let E : Set (TiltedConfiguration N t) := {ω | ¬ ∃ x : ℤ, x<0 ∧ FullyOpenColumn N t x ω}
  have hbound (L : ℕ) : μ.real E ≤ (1-openColumnCost q N)^L := by
    apply le_trans (measureReal_mono (μ := μ) (s₂ := {ω | ∀ j<L,
      ¬FullyOpenColumn N t (-(L:ℤ)+(j:ℤ)) ω}) ?_)
      (selfDualTiltedStrip_noOpenColumns_le q N t (-(L:ℤ)) L)
    intro ω hω j hj hfull
    exact hω ⟨-(L:ℤ)+(j:ℤ),by omega,hfull⟩
  have hconv : Tendsto (fun L : ℕ => (1-openColumnCost q N)^L) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (openColumnFailureFactor_bounds q N).1
      (openColumnFailureFactor_bounds q N).2
  have hz : μ.real E=0 := le_antisymm
    (ge_of_tendsto hconv (Eventually.of_forall hbound)) ENNReal.toReal_nonneg
  apply ae_iff.mpr
  exact (measureReal_eq_zero_iff (measure_ne_top μ E)).mp hz

/-- Two actual fully open columns cut off the central column almost surely. -/
theorem ae_exists_fullyOpenColumns_both_sides (q : Set.Ici (1 : ℝ)) (N : ℕ) (t : ℝ) :
    ∀ᵐ ω ∂(selfDualTiltedStripMeasure q N t), ∃ xminus xplus : ℤ,
      xminus<0 ∧ 0<xplus ∧ FullyOpenColumn N t xminus ω ∧ FullyOpenColumn N t xplus ω := by
  filter_upwards [ae_exists_fullyOpenColumn_left q N t,ae_exists_fullyOpenColumn_right q N t]
    with ω hleft hright
  obtain ⟨xm,hxm,hm⟩ := hleft
  obtain ⟨xp,hxp,hp⟩ := hright
  exact ⟨xm,xp,hxm,hxp,hm,hp⟩

end
end PottsContinuity.PlanarMixed.TiltedHalfHeight
