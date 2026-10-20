module

public import PottsContinuity.PlanarMixed.FiniteSlit.ActiveMarginal
public import PottsContinuity.PlanarMixed.FiniteSlit.InducedBoundaryUpper
public import PottsContinuity.PlanarMixed.FiniteSlit.Comparison

/-! The canonical finite complementary image is dominated by the explicitly
joined dual FK law. No dual-law or boundary identification premise remains. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.Duality BD12 MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Exact induced law, boundary domination and isolated-face removal give
canonical dual domination for every increasing sampled event. -/
theorem dual_image_probability_le_canonical (θ : Parameters)
    (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ))
    (T : Set (Configuration (dualGraph M x y))) (hT : IsUpperSet T) :
    (measure (graph M x y) θ (boundary M x y hM hy hyM)
      (dualConfiguration M x y ⁻¹' T)).toReal ≤
    (measure (dualGraph M x y) (dualParameters θ) (dualBoundary M x y) T).toReal := by
  have htransfer := congrArg (fun ρ : PMF (Configuration (dualGraph M x y)) => ρ.toMeasure T)
    (law_map_dual_eq_induced θ M x y hM hy hyM)
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    MeasurableSpace.measurableSet_top] at htransfer
  change (law _ _ _).toMeasure _ = (law _ _ _).toMeasure _ at htransfer
  change ((law _ _ _).toMeasure _).toReal ≤ _
  rw [htransfer]
  have hbound := measure_boundary_comparison (G := dualGraph M x y) (dualParameters θ)
    (inducedDualBoundary M x y hM)
    (BoundaryCondition.wired ((dualBottom M x ∪ dualRay M x y) ∪ irrelevantExterior M x))
    (inducedDualBoundary_partition_le_extra M x y hM hy hyM) T hT
  have hsame : measure (dualGraph M x y) (dualParameters θ)
      (BoundaryCondition.wired ((dualBottom M x ∪ dualRay M x y) ∪ irrelevantExterior M x)) T =
      measure (dualGraph M x y) (dualParameters θ) (dualBoundary M x y) T := by
    unfold PD.FK.measure
    rw [dual_law_extra_exterior_wiring_eq (dualParameters θ) M x y hM]
  rw [hsame] at hbound
  exact hbound

/-- The dual-law premise is DISCHARGED. Only deterministic finite dual crossing
existence remains for the uniform finite mixed estimate. -/
theorem wired_arcs_lower_bound_of_dualExistence (q : Set.Ici (1 : ℝ))
    (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ))
    (hexists : ∀ C : Configuration (graph M x y), C ∉ connectionEvent M x y →
      dualConfiguration M x y C ∈
        arcsConnectionEvent (dualGraph M x y) (dualBottom M x) (dualRay M x y)) :
    1/(1+(q : ℝ)^2) ≤
      (measure (graph M x y) (criticalParameters q) (boundary M x y hM hy hyM)
        (connectionEvent M x y)).toReal := by
  let μ := measure (graph M x y) (criticalParameters q) (boundary M x y hM hy hyM)
  let S := connectionEvent M x y
  let T := arcsConnectionEvent (dualGraph M x y) (dualBottom M x) (dualRay M x y)
  have hmono := ENNReal.toReal_mono (measure_ne_top μ _)
    (measure_mono (μ := μ) (show Sᶜ ⊆ dualConfiguration M x y ⁻¹' T from hexists))
  have himage := dual_image_probability_le_canonical (criticalParameters q)
    M x y hM hy hyM T (arcsConnectionEvent_isUpperSet _ _)
  rw [dualParameters_criticalParameters] at himage
  have hsum := probReal_add_probReal_compl (μ := μ) (s := S) MeasurableSpace.measurableSet_top
  have hc := dual_connection_probability_le_q_sq q M x y hM hy hyM
  apply (div_le_iff₀ (by positivity : 0 < 1+(q : ℝ)^2)).mpr
  change (μ S).toReal + (μ Sᶜ).toReal = 1 at hsum
  change (measure (dualGraph M x y) (criticalParameters q) (dualBoundary M x y) T).toReal ≤
    (q : ℝ)^2*(μ S).toReal at hc
  have hweak := hmono.trans (himage.trans hc)
  nlinarith only [hsum,hweak]

end
end PottsContinuity.PlanarMixed.FiniteSlit
