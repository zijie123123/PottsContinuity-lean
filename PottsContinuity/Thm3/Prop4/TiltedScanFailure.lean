module

public import PottsContinuity.Thm3.Prop4.TiltedTwoCutReveal

/-! # Quantitative probability of failed two-sided tilted-cut exploration -/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm3.Prop4

noncomputable section

local instance scanFailureEdgeFintype (n M : ℕ) (t : ℝ) :
    Fintype (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _

/-- Any injectively ordered finite list of columns has the same scan failure
bound, including a right-to-left scan. -/
theorem tiltedCutScan_failure_le_of_injective (θ : PD.FK.Parameters) (n M : ℕ) (t : ℝ)
    (ξ : PD.FK.BoundaryCondition (tiltedWindow n M t : Set (ℤ × ℤ)))
    (c : ℕ → ℤ) (hc : Function.Injective c) (K : ℕ) :
    (PD.FK.measure (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))) θ ξ
      {A | (tiltedCutScan n M t c K A).2 = none}).toReal ≤
        (1-(1-PD.FK.edgeParameter θ)^(n+1))^K := by
  rw [tiltedCutScan_none_event]
  apply closedCutFailure_probability_le_of_card
  · intro i _ j _ hij
    exact tiltedWindowCutEdges_disjoint n M t (c i) (c j) (fun h => hij (hc h))
  · intro i _
    exact tiltedWindowCutEdges_card_le n M t (c i)

/-- The two-sided exploration fails exactly when at least one actual scan fails. -/
theorem tiltedTwoCutBounds_none_event (n M : ℕ) (t : ℝ) (a b : ℤ) (K : ℕ) :
    {A | tiltedTwoCutBounds n M t a b K A = none} =
      {A | (tiltedCutScan n M t (fun i => a+i) K A).2 = none} ∪
      {A | (tiltedCutScan n M t (fun i => b-i) K A).2 = none} := by
  ext A
  cases hL : (tiltedCutScan n M t (fun i => a+i) K A).2 <;>
    cases hR : (tiltedCutScan n M t (fun i => b-i) K A).2 <;>
    simp [tiltedTwoCutBounds,hL,hR]

/-- Uniform two-sided failure estimate under every outer boundary partition. -/
theorem tiltedTwoCut_failure_probability_le (θ : PD.FK.Parameters) (n M : ℕ) (t : ℝ)
    (ξ : PD.FK.BoundaryCondition (tiltedWindow n M t : Set (ℤ × ℤ)))
    (a b : ℤ) (K : ℕ) :
    (PD.FK.measure (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))) θ ξ
      {A | tiltedTwoCutBounds n M t a b K A = none}).toReal ≤
        2*(1-(1-PD.FK.edgeParameter θ)^(n+1))^K := by
  have hL := tiltedCutScan_failure_le_of_injective θ n M t ξ (fun i => a+i)
    (fun i j h => by dsimp only at h; omega) K
  have hR := tiltedCutScan_failure_le_of_injective θ n M t ξ (fun i => b-i)
    (fun i j h => by dsimp only at h; omega) K
  rw [tiltedTwoCutBounds_none_event]
  have h := (measureReal_union_le (μ := PD.FK.measure _ θ ξ)
    {A | (tiltedCutScan n M t (fun i => a+i) K A).2 = none}
    {A | (tiltedCutScan n M t (fun i => b-i) K A).2 = none}).trans (add_le_add hL hR)
  simpa only [Measure.real,two_mul] using h

/-- The actual scan error tends to zero exponentially in the number of cuts. -/
theorem tilted_scan_error_tendsto_zero (θ : PD.FK.Parameters) (n : ℕ) :
    Tendsto (fun K : ℕ => 2*(1-(1-PD.FK.edgeParameter θ)^(n+1))^K) atTop (𝓝 0) := by
  have hρ0 := (PD.FK.one_sub_edgeParameter_pos θ).le
  have hρ1 : 1-PD.FK.edgeParameter θ ≤ 1 := by linarith only [PD.FK.edgeParameter_pos θ]
  have hbase0 : 0 ≤ 1-(1-PD.FK.edgeParameter θ)^(n+1) :=
    sub_nonneg.mpr (pow_le_one₀ hρ0 hρ1)
  have hbase1 : 1-(1-PD.FK.edgeParameter θ)^(n+1) < 1 :=
    sub_lt_self _ (pow_pos (PD.FK.one_sub_edgeParameter_pos θ) _)
  simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1).const_mul (2 : ℝ)

end

end PottsContinuity.Thm3.Prop4
