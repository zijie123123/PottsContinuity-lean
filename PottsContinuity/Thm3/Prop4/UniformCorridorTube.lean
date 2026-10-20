module

public import PottsContinuity.Thm3.Prop4.CorridorScale

/-!
# Uniform actual wired-plane tube crossings

The cutoff depends only on the assumed decay parameters and fractional
exponent. Every genuine opposite-face endpoint pair is covered, including
segments meeting the top or bottom of the original box.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

/-- A single numerical cutoff makes the concrete rounded corridor admissible
and its failure bound at most one half. -/
theorem exists_uniform_corridor_scale (c₀ α ε : ℝ)
    (hc₀ : 0 < c₀) (hα : 0 < α) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      1 ≤ ⌊(n : ℝ)^ε/2⌋₊ ∧ ⌊(n : ℝ)^ε/2⌋₊ ≤ n ∧
      4*(⌊(n : ℝ)^ε/2⌋₊ : ℝ)+1 ≤ 4*(n : ℝ)^ε ∧
      (10*(n : ℝ)+2)*(⌊(n : ℝ)^ε/2⌋₊ : ℝ)*
        Real.exp (-c₀*((⌊(n : ℝ)^ε/2⌋₊ : ℝ)+1)^α) ≤ 1/2 := by
  have he := (corridor_fractional_error_tendsto_zero c₀ α ε hc₀ hα hε).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  have hr := ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (2 : ℝ))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (he.and hr)
  refine ⟨max N 1,le_max_right _ _,?_⟩
  intro n hn
  have hn1 := (le_max_right N 1).trans hn
  obtain ⟨he',hr'⟩ := hN n ((le_max_left _ _).trans hn)
  obtain ⟨hs,hsn,hR⟩ := corridor_half_radius_floor_bounds hn1 hε1 hr'
  exact ⟨hs,hsn,hR,(corridor_half_radius_error_le hn1 c₀ α ε hc₀ hα).trans he'.le⟩

/-- The actual radius-four tube crosses with wired-plane probability at least
one half at every sufficiently large scale, for all real cluster weights. -/
theorem selfDual_wired_tube_crossing_uniform_ge_half
    (c₀ α ε : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (q : Set.Ici (1 : ℝ)) (μ₀ μ₁ : Measure LatticeConfiguration),
      IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ₀ →
      IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 1 μ₁ →
      (∀ m : ℕ, 1 ≤ m → RSW.oneArmProbability μ₀ m ≤ Real.exp (-c₀*(m : ℝ)^α)) →
      ∀ n : ℕ, N ≤ n → ∀ u v : LatticeVertex, u ∈ box n → v ∈ box n →
      u.1 = -(n : ℤ) → v.1 = (n : ℤ) →
      1/2 ≤ μ₁.real (tubeHorizontalCrossingEvent n (4*(n : ℝ)^ε) u v) := by
  obtain ⟨N,hN,hscale⟩ := exists_uniform_corridor_scale c₀ α ε hc₀ hα hε hε1
  refine ⟨N,hN,?_⟩
  intro q μ₀ μ₁ hμ₀ hμ₁ hdecay n hn u v hu hv ha hb
  let : IsProbabilityMeasure μ₁ := hμ₁.1
  have hn1 := hN.trans hn
  obtain ⟨hs,hsn,hR,herror⟩ := hscale n hn
  obtain ⟨t,b,ht,huL,hvL⟩ := inductionTube_supporting_line hn1 u v hu hv ha hb
  have hfail := (selfDual_wired_tube_noncrossing_le_corridor_error q μ₀ μ₁ hμ₀ hμ₁
    c₀ α hc₀ hα hdecay hn1 ⌊(n : ℝ)^ε/2⌋₊ hsn hs u v hu hv ha hb
    t b ht huL hvL (4*(n : ℝ)^ε) hR).trans herror
  rw [measureReal_compl (tubeHorizontalCrossingEvent_isCylinder n (4*(n : ℝ)^ε) u v).measurableSet,
    probReal_univ] at hfail
  linarith only [hfail]

end
end PottsContinuity.Thm3.Prop4
