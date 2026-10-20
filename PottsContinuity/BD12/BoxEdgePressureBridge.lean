module

public import PottsContinuity.BD12.DRTEventProbability
public import PottsContinuity.BD12.DRTLogActivity
public import PottsContinuity.Infinite.Bridge
public import PottsContinuity.PD.RCInfinite.LimitComparison

/-! Actual finite-box edge means and their infinite-volume comparisons. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite MeasureTheory
open scoped Classical BigOperators
noncomputable section
local instance boxPressureEdges (n : ℕ) : Fintype (boxGraph (0,0) n).edgeSet := Fintype.ofFinite _

/-- Every sampled box edge has exactly its homogeneous finite-law intensity,
under either exterior extension convention. -/
theorem drt_box_edge_mean_eq_probability
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (β : Set.Ioi (0 : ℝ))
    (i : Fin 2) (n : ℕ) (e : (boxGraph (0,0) n).edgeSet) :
    drtMean (boxGraph (0,0) n) q (boxBoundary i (0,0) n)
      (fun _ => ⟨(1 : ℝ), (show (0 : ℝ) < 1 from one_pos)⟩) β
      (drtEdgeIndicator (boxGraph (0,0) n) e) =
    (boxMeasure (drtHomogeneousParameters q hq β) i (0,0) n :
      Measure LatticeConfiguration).real
      (LatticeConfiguration.allOpen {boxEdgeEmbedding (0,0) n e}) := by
  let A : Set (Configuration (boxGraph (0,0) n)) := {C | e ∈ C}
  have hi : A.indicator (fun _ => (1 : ℝ)) = drtEdgeIndicator (boxGraph (0,0) n) e := by
    funext C
    by_cases hC : e ∈ C <;> simp [A, Set.indicator, drtEdgeIndicator, hC]
  have hp : (boxExtension i (0,0) n) ⁻¹'
      (LatticeConfiguration.allOpen {boxEdgeEmbedding (0,0) n e}) = A := by
    ext C
    simp [LatticeConfiguration.allOpen, boxExtension_at, A]
  rw [← hi, drt_mean_indicator_eq_fk_probability]
  rw [Measure.real, boxMeasure_apply _ i (0,0) n (isCylinder_allOpen _).measurableSet, hp]

/-- Wired infinite edge intensity is below the actual sampled wired box mean. -/
theorem wired_infinite_edge_le_box_mean
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (β : Set.Ioi (0 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (drtHomogeneousParameters q hq β).toP
      (drtHomogeneousParameters q hq β).toQ 1 μ)
    (n : ℕ) (e : (boxGraph (0,0) n).edgeSet) :
    μ.real (LatticeConfiguration.allOpen {boxEdgeEmbedding (0,0) n e}) ≤
      drtMean (boxGraph (0,0) n) q (boxBoundary 1 (0,0) n)
        (fun _ => ⟨(1 : ℝ), (show (0 : ℝ) < 1 from one_pos)⟩) β
        (drtEdgeIndicator (boxGraph (0,0) n) e) := by
  let : IsProbabilityMeasure μ := hμ.1
  rw [drt_box_edge_mean_eq_probability q hq β]
  have hF : ({boxEdgeEmbedding (0,0) n e} : Set Edge) ⊆ boxEdges (0,0) n := by
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    exact ⟨e,hf.symm⟩
  have h := wired_limit_joint_le (drtHomogeneousParameters q hq β) μ
    (Infinite.isRCInfiniteVolumeLimit_to_PD_box _ _ _ _ hμ) n
    {boxEdgeEmbedding (0,0) n e} (by simpa using hF) Set.univ
    ⟨∅,fun _ _ _ => Iff.rfl⟩ (fun _ _ _ => Iff.rfl)
  simpa only [Set.inter_univ, Measure.real, measure_univ, ENNReal.toReal_one, mul_one, boxMeasure_wired] using h

/-- The actual sampled free box edge mean is below its free infinite intensity. -/
theorem free_box_edge_mean_le_infinite
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (β : Set.Ioi (0 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (drtHomogeneousParameters q hq β).toP
      (drtHomogeneousParameters q hq β).toQ 0 μ)
    (n : ℕ) (e : (boxGraph (0,0) n).edgeSet) :
    drtMean (boxGraph (0,0) n) q (boxBoundary 0 (0,0) n)
      (fun _ => ⟨(1 : ℝ), (show (0 : ℝ) < 1 from one_pos)⟩) β
      (drtEdgeIndicator (boxGraph (0,0) n) e) ≤
    μ.real (LatticeConfiguration.allOpen {boxEdgeEmbedding (0,0) n e}) := by
  let : IsProbabilityMeasure μ := hμ.1
  rw [drt_box_edge_mean_eq_probability q hq β]
  have hF : ({boxEdgeEmbedding (0,0) n e} : Set Edge) ⊆ boxEdges (0,0) n := by
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    exact ⟨e,hf.symm⟩
  have h := free_limit_joint_ge (drtHomogeneousParameters q hq β) μ
    (Infinite.isRCInfiniteVolumeLimit_to_PD_box _ _ _ _ hμ) n
    {boxEdgeEmbedding (0,0) n e} (by simpa using hF) Set.univ
    ⟨∅,fun _ _ _ => Iff.rfl⟩ (fun _ _ _ => Iff.rfl)
  simpa only [Set.inter_univ, Measure.real, measure_univ, ENNReal.toReal_one, mul_one, boxMeasure_free] using h

end
end PottsContinuity.BD12
