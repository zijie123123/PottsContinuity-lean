module

public import PottsContinuity.Thm3.Prop4.TiltedStoppedCylinders
public import PottsContinuity.Thm3.Prop4.TiltedIntervalInterior
public import PottsContinuity.Thm3.Prop4.TiltedScanFailure
public import PottsContinuity.Thm3.Prop4.TiltedRecordSuccess
public import PottsContinuity.Thm3.RSW.StoppingUpper

/-! # Averaging actual stopped cylinders with the geometric scan error -/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.RCInfinite

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance cylinderUpperEdgeFintype (n M : ℕ) (t : ℝ) :
    Fintype (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _
local instance cylinderUpperEdgeDecidableEq (n M : ℕ) (t : ℝ) :
    DecidableEq (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Classical.decEq _

/-- The genuine mixed-boundary finite cylinder is at most its top-only limit
plus the explicit two-scan error. Every exploration and conditional comparison
used here is a proved dependency. -/
theorem tilted_window_allOpen_le_limit_add_error (θ : Parameters)
    (n M R K : ℕ) (hscale : M = n+R+K) (t : ℝ) (ht : |t| ≤ 1) (side : Fin 2)
    (ν : ProbabilityMeasure LatticeConfiguration)
    (hν : Tendsto (tiltedWindowPlaneProbabilityMeasure θ n t 0) atTop (𝓝 ν))
    (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (frozenEdgeEmbedding (tiltedWindow n R t))) :
    (measure (finiteLatticeGraph (tiltedWindow n M t)) θ (tiltedWindowBoundary n M t side)
      (finiteSubgraphOpenEvent (tiltedWindow n M t) F)).toReal ≤
        ν.toMeasure.real (LatticeConfiguration.allOpen F)+2*(1-(1-edgeParameter θ)^(n+1))^K := by
  classical
  let G := finiteLatticeGraph (tiltedWindow n M t)
  let ξ := tiltedWindowBoundary n M t side
  let a : ℤ := -(M : ℤ)+n
  let b : ℤ := (M : ℤ)-n-1
  let reveal := tiltedTwoCutReveal n M t a b K
  let E := finiteSubgraphOpenEvent (tiltedWindow n M t) F
  let good : Set (Configuration G) := {A | tiltedTwoCutBounds n M t a b K A ≠ none}
  let bad : Set (Configuration G) := {A | tiltedTwoCutBounds n M t a b K A = none}
  have hgood : (measure G θ ξ (E ∩ good)).toReal ≤ ν.toMeasure.real (LatticeConfiguration.allOpen F) := by
    apply RSW.stopped_event_upper_of_record_bounds θ ξ reveal
      (tiltedTwoCutReveal_stable n M t a b K)
    intro A₀
    let P := (law G θ ξ).filter (Exploration.revealRecordEvent reveal A₀)
      ⟨A₀,⟨rfl,rfl⟩,(law_pos G θ ξ A₀).ne'⟩
    change (P.toMeasure (E ∩ good)).toReal ≤ _
    by_cases hg : tiltedTwoCutBounds n M t a b K A₀ = none
    · have hzero : P.toMeasure (E ∩ good) = 0 := by
        apply (P.toMeasure_apply_eq_zero_iff MeasurableSpace.measurableSet_top).mpr
        apply Set.disjoint_left.mpr
        intro A hA hEg
        have hr := (PMF.mem_support_filter_iff (h :=
          (show ∃ A ∈ Exploration.revealRecordEvent reveal A₀, A ∈ (law G θ ξ).support from
            ⟨A₀,⟨rfl,rfl⟩,(law_pos G θ ξ A₀).ne'⟩))).mp hA
        have heq := tiltedTwoCutBounds_eq_on_record n M t a b K A₀ A hr.1
        exact hEg.2 (heq.trans hg)
      rw [hzero,ENNReal.toReal_zero]
      exact ENNReal.toReal_nonneg
    · cases hL : (tiltedCutScan n M t (fun r => a+r) K A₀).2 with
      | none => exact False.elim (hg (by simp [tiltedTwoCutBounds,hL]))
      | some i =>
        cases hR : (tiltedCutScan n M t (fun r => b-r) K A₀).2 with
        | none => exact False.elim (hg (by simp [tiltedTwoCutBounds,hR]))
        | some j =>
          have hi := (tiltedCutScan_hit n M t (fun r => a+r) K A₀ i hL).1
          have hj := (tiltedCutScan_hit n M t (fun r => b-r) K A₀ j hR).1
          have hsub : tiltedWindow n R t ⊆ tiltedInterval n M t (a+i+1) (b-j) := by
            intro z hz
            have hzM := tiltedWindow_mono n t (show R ≤ M by omega) hz
            have hx := ((Foundations.mem_box_iff_abs_le R z).mp ((mem_tiltedWindow n R t z).mp hz).1).1
            exact scanned_tiltedInterval_contains_center n M R K hscale i j hi hj t z hzM hx
          have hFinner : ∀ e ∈ F, e ∈ Set.range (frozenEdgeEmbedding (tiltedInterval n M t (a+i+1) (b-j))) :=
            fun e he => frozenEdgeEmbedding_range_mono hsub (hF e he)
          have hcond := tiltedTwoCutRecord_allOpen_le_limit θ n M t a b K side A₀ i j hL hR
            (scanned_tiltedInterval_avoids_boxBoundary n M t ht i j) ν hν F hFinner
          exact (measureReal_mono (μ := P.toMeasure) (Set.inter_subset_left : E ∩ good ⊆ E)).trans hcond
  have hbad : (measure G θ ξ bad).toReal ≤ 2*(1-(1-edgeParameter θ)^(n+1))^K :=
    tiltedTwoCut_failure_probability_le θ n M t ξ a b K
  have hsub : E ⊆ (E ∩ good) ∪ bad := by
    intro A hA
    by_cases h : tiltedTwoCutBounds n M t a b K A = none
    · exact Or.inr h
    · exact Or.inl ⟨hA,h⟩
  have hmass := (measureReal_mono (μ := measure G θ ξ) hsub).trans
    (measureReal_union_le (μ := measure G θ ξ) (E ∩ good) bad)
  exact hmass.trans (add_le_add hgood hbad)

end

end PottsContinuity.Thm3.Prop4
