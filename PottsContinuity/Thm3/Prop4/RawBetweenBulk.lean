module

public import PottsContinuity.Thm3.Prop4.RawBetweenCoreLower
public import PottsContinuity.Thm3.Prop4.FiniteStrictCore
public import PottsContinuity.Thm3.Prop4.TubeSquaredArmBound

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite Push Exploration
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance rawBetweenBulkEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _

/-- The actual source between-event bulk bound, with only the touching
estimate external. The full raw replay and its conditional law are proved. -/
theorem between_trace_bulk_bound_of_touch
    (q : Set.Ici (1 : ℝ)) (c₀ α ε : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ)
    (hdecay : ∀ m : ℕ, 1 ≤ m → RSW.oneArmProbability μ m ≤ Real.exp (-c₀*(m : ℝ)^α))
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    ∃ A C : ℝ, ∃ N : ℕ, 0 < A ∧ 0 < C ∧ 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ u v : (box n : Set LatticeVertex),
      u.val.1 = -(n : ℤ) → v.val.1 = n →
      ∀ η : ℝ, (n : ℝ)^η = 4*(n : ℝ)^ε →
      (measure (finiteLatticeGraph (box n)) (RSW.selfDualParameters q) (BoundaryCondition.free ∅)
        (betweenTubeTraceEvent n η u v (markedLowerBoxTrace n u v) (markedUpperBoxTrace n u v))).toReal ≤
        A*Real.exp (C*(n : ℝ)^ε)*(RSW.oneArmProbability μ n)^2 := by
  obtain ⟨A,C,hA,hC,hTube⟩ := widened_tube_connection_squared_arm_bound_of_touch q ε hε μ hμ hTouch
  obtain ⟨N,hN,hcore⟩ := selfDual_wired_box_strict_core_uniform_ge_half c₀ α ε hc₀ hα hε hε1
  refine ⟨2*A,C,N,mul_pos (by norm_num) hA,hC,hN,?_⟩
  intro n hn u v hu hv η hη
  obtain ⟨t,b,ht,hut,hvt⟩ := inductionTube_supporting_line (hN.trans hn) u.val v.val
    u.property v.property hu hv
  let H : Set (Configuration (finiteLatticeGraph (box n))) :=
    {B | ∃ p : (openGraph _ B).Walk u v,
      ∀ z ∈ p.support, z.val ∈ radiusTube n (4*(n : ℝ)^ε) u.val v.val}
  have hbetween := between_trace_core_probability_mul_le_confined n (hN.trans hn) η u v hu hv t b ht hut hvt
    (RSW.selfDualParameters q)
  rw [hη] at hbetween
  have hlower := (mul_le_mul_of_nonneg_right
    (hcore q μ hμ hdecay n hn u.val v.val u.property v.property hu hv t b ht hut hvt)
    (show 0 ≤ (measure (finiteLatticeGraph (box n)) (RSW.selfDualParameters q) (BoundaryCondition.free ∅)
      (betweenTubeTraceEvent n η u v (markedLowerBoxTrace n u v) (markedUpperBoxTrace n u v))).toReal from ENNReal.toReal_nonneg)).trans hbetween
  have hupper := hTube n (hN.trans hn) u v hu hv
  calc
    _ = 2*((1/2)*(measure (finiteLatticeGraph (box n)) (RSW.selfDualParameters q)
      (BoundaryCondition.free ∅) (betweenTubeTraceEvent n η u v
        (markedLowerBoxTrace n u v) (markedUpperBoxTrace n u v))).toReal) := by ring
    _ ≤ 2*(measure (finiteLatticeGraph (box n)) (RSW.selfDualParameters q) (BoundaryCondition.free ∅) H).toReal :=
      mul_le_mul_of_nonneg_left hlower (by norm_num)
    _ ≤ 2*(A*Real.exp (C*(n : ℝ)^ε)*(RSW.oneArmProbability μ n)^2) :=
      mul_le_mul_of_nonneg_left hupper (by norm_num)
    _ = _ := by ring

end
end PottsContinuity.Thm3.Prop4
