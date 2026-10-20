module

public import PottsContinuity.Thm3.RSW.ClosedBlockFailure
public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutFailure
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory Filter Topology FKC.Medial
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance stripClosedCutFailureEdgeEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _

/-- The literal original left closed-cut scan has a uniform failure estimate
for every FK parameter and every finite boundary partition. -/
theorem strip_left_closed_cut_failure_le
    (θ : Parameters) (N n K : ℕ) (hKN : K ≤ N)
    (ξ : BoundaryCondition (FKC.RectangleVertex (-(N:ℤ),0) (2*N) (2*n))) :
    (measure (horizontalStripCutRectangle N n) θ ξ
      {A | (horizontalStripLeftBlockScan N n K A).2 = none}).toReal ≤
      (1-(1-edgeParameter θ)^(2*n+1))^(N-K) := by
  have h := firstClosedBlockScan_none_probability_le_constant_card θ ξ (List.range (N-K))
    (horizontalStripLeftCutBlock N n K) (2*n+1)
    (by
      intro i hi j hj hij
      exact horizontalStripLeftCutBlock_disjoint N n K hKN
        (List.mem_range.mp (List.mem_toFinset.mp hi))
        (List.mem_range.mp (List.mem_toFinset.mp hj)) hij)
    (by
      intro i hi
      exact horizontalStripLeftCutBlock_card N n K hKN
        (List.mem_range.mp (List.mem_toFinset.mp hi)))
  have hlen : (List.range (N-K)).toFinset.card = N-K := by
    rw [List.toFinset_card_of_nodup List.nodup_range,List.length_range]
  simpa only [horizontalStripLeftBlockScan,hlen] using h

/-- The original right scan obeys the same bound on the same full carrier. -/
theorem strip_right_closed_cut_failure_le
    (θ : Parameters) (N n K : ℕ) (hKN : K ≤ N)
    (ξ : BoundaryCondition (FKC.RectangleVertex (-(N:ℤ),0) (2*N) (2*n))) :
    (measure (horizontalStripCutRectangle N n) θ ξ
      {A | (horizontalStripRightBlockScan N n K A).2 = none}).toReal ≤
      (1-(1-edgeParameter θ)^(2*n+1))^(N-K) := by
  have h := firstClosedBlockScan_none_probability_le_constant_card θ ξ (List.range (N-K))
    (horizontalStripRightCutBlock N n K) (2*n+1)
    (by
      intro i hi j hj hij
      exact horizontalStripRightCutBlock_disjoint N n K hKN
        (List.mem_range.mp (List.mem_toFinset.mp hi))
        (List.mem_range.mp (List.mem_toFinset.mp hj)) hij)
    (by
      intro i hi
      exact horizontalStripRightCutBlock_card N n K hKN
        (List.mem_range.mp (List.mem_toFinset.mp hi)))
  have hlen : (List.range (N-K)).toFinset.card = N-K := by
    rw [List.toFinset_card_of_nodup List.nodup_range,List.length_range]
  simpa only [horizontalStripRightBlockScan,hlen] using h

/-- A union bound for the TWO actual scans, uniform over all outer states
and boundary partitions. The cut geometry is imported unchanged. -/
theorem strip_either_closed_cut_failure_le
    (θ : Parameters) (N n K : ℕ) (hKN : K ≤ N)
    (ξ : BoundaryCondition (FKC.RectangleVertex (-(N:ℤ),0) (2*N) (2*n))) :
    (measure (horizontalStripCutRectangle N n) θ ξ
      {A | (horizontalStripLeftBlockScan N n K A).2 = none ∨
        (horizontalStripRightBlockScan N n K A).2 = none}).toReal ≤
      2*(1-(1-edgeParameter θ)^(2*n+1))^(N-K) := by
  let μ := measure (horizontalStripCutRectangle N n) θ ξ
  let L : Set (Configuration (horizontalStripCutRectangle N n)) :=
    {A | (horizontalStripLeftBlockScan N n K A).2 = none}
  let R : Set (Configuration (horizontalStripCutRectangle N n)) :=
    {A | (horizontalStripRightBlockScan N n K A).2 = none}
  have hU := measureReal_union_le (μ := μ) L R
  have hL := strip_left_closed_cut_failure_le θ N n K hKN ξ
  have hR := strip_right_closed_cut_failure_le θ N n K hKN ξ
  change μ.real (L ∪ R) ≤ _ at hU
  change μ.real L ≤ _ at hL
  change μ.real R ≤ _ at hR
  change μ.real (L ∪ R) ≤ _
  calc
    _ ≤ μ.real L+μ.real R := hU
    _ ≤ (1-(1-edgeParameter θ)^(2*n+1))^(N-K)+
        (1-(1-edgeParameter θ)^(2*n+1))^(N-K) := add_le_add hL hR
    _ = _ := by ring

/-- For each fixed strip height and central collar, failed cut exploration
vanishes for EVERY sequence of original boundary conditions, all real q>=1. -/
theorem strip_closed_cut_failure_tendsto_zero
    (θ : Parameters) (n K : ℕ)
    (ξ : ∀ N : ℕ, BoundaryCondition (FKC.RectangleVertex (-(N:ℤ),0) (2*N) (2*n))) :
    Tendsto (fun N => (measure (horizontalStripCutRectangle N n) θ (ξ N)
      {A | (horizontalStripLeftBlockScan N n K A).2 = none ∨
        (horizontalStripRightBlockScan N n K A).2 = none}).toReal) atTop (𝓝 0) := by
  let ρ := 1-(1-edgeParameter θ)^(2*n+1)
  have hp0 : 0 ≤ 1-edgeParameter θ := by have := edgeParameter_lt_one θ; linarith
  have hp1 : 1-edgeParameter θ ≤ 1 := by have := edgeParameter_pos θ; linarith
  have hρ0 : 0 ≤ ρ := by
    have hh : (1-edgeParameter θ)^(2*n+1) ≤ 1 := pow_le_one₀ hp0 hp1
    dsimp [ρ]
    linarith
  have hρ1 : ρ < 1 := by
    have hh : 0 < (1-edgeParameter θ)^(2*n+1) :=
      pow_pos (by have := edgeParameter_lt_one θ; linarith) _
    dsimp [ρ]
    linarith
  have hsub : Tendsto (fun N : ℕ => N-K) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (K+b)] with N hN
    omega
  have ht : Tendsto (fun N : ℕ => 2*ρ^(N-K)) atTop (𝓝 ((2:ℝ)*0)) := tendsto_const_nhds.mul
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp hsub)
  have hb : ∀ᶠ N : ℕ in atTop,
      (measure (horizontalStripCutRectangle N n) θ (ξ N)
        {A | (horizontalStripLeftBlockScan N n K A).2 = none ∨
          (horizontalStripRightBlockScan N n K A).2 = none}).toReal ≤ 2*ρ^(N-K) := by
    filter_upwards [eventually_ge_atTop K] with N hN
    exact strip_either_closed_cut_failure_le θ N n K hN (ξ N)
  apply squeeze_zero' (Eventually.of_forall (fun N => ENNReal.toReal_nonneg)) hb
  simpa only [mul_zero] using ht

end
end PottsContinuity.RSW
