module

public import PottsContinuity.Thm3.RSW.StripSourceCylinderNormalization

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory Filter Topology FKC.Medial
noncomputable section

/-- Exact source-cylinder probabilities forget the specified lateral wiring
at every fixed strip height, for all interior parameters and every q>=1. -/
theorem stripWindowCylinderProbability_boundary_difference_tendsto_zero
    (θ : Parameters) (n : ℕ) (i : Fin 2)
    (A : Finset (stripGraph n).edgeSet) (ξ : StripConfiguration n) :
    Tendsto (fun M => stripWindowCylinderProbability θ n i M A ξ -
      stripWindowCylinderProbability θ n 0 M A ξ) atTop (𝓝 0) := by
  obtain ⟨K,hO,hC⟩ := stripNormalizedPattern_exists_support n A ξ
  have h := stripWindow_pattern_boundary_difference_tendsto_zero θ n K i
    (stripNormalizedOpenPattern n A ξ) (stripNormalizedClosedPattern n A ξ) hO hC
  apply h.congr'
  filter_upwards [eventually_stripWindow_finset_edge_lift n A] with M hM
  rw [stripWindowCylinderProbability_normalized_pattern θ n M i A ξ hM,
    stripWindowCylinderProbability_normalized_pattern θ n M 0 A ξ hM]

/-- The two actual source lateral conventions define exactly the same
strip-cylinder limit predicate. No common limit is postulated. -/
theorem isTopWiredStripLimit_iff_top (θ : Parameters) (n : ℕ) (i : Fin 2)
    (μ : Measure (StripConfiguration n)) :
    IsTopWiredStripLimit θ n i μ ↔ IsTopWiredStripLimit θ n 0 μ := by
  constructor
  · intro hμ
    refine ⟨hμ.1,?_⟩
    intro A ξ
    have h := (hμ.2 A ξ).sub
      (stripWindowCylinderProbability_boundary_difference_tendsto_zero θ n i A ξ)
    simp only [sub_zero] at h
    convert h using 1
    funext M
    ring
  · intro hμ
    refine ⟨hμ.1,?_⟩
    intro A ξ
    have h := (stripWindowCylinderProbability_boundary_difference_tendsto_zero θ n i A ξ).add
      (hμ.2 A ξ)
    simpa only [zero_add,sub_add_cancel] using h

end
end PottsContinuity.RSW
