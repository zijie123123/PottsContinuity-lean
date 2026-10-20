module

public import PottsContinuity.PlanarTopology.HalfPlaneBoundaryFiniteness
public import PottsContinuity.PlanarTopology.HalfPlaneLeftmostRoot
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Int.Star
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

/-- Under translation invariance and positive association, almost-sure
uniqueness and existence of the actual dual infinite cluster exclude every
infinite component of the original configuration restricted to a right half-plane. -/
theorem halfPlane_no_infinite_cluster_ae
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hinfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent) :
    ∀ᵐ ω ∂μ, ∀ u : {z : LatticeVertex // 0 ≤ z.1}, ω ∉ halfPlaneInfiniteAt u := by
  have hB := halfPlane_finite_unit_ae μ htranslation hFKG hunique hinfinite
  have hT (a : LatticeVertex) : ∀ᵐ ω ∂μ, edgeTranslate a ω ∈ halfPlaneFiniteUnitEvent := by
    have hB' : ∀ᵐ η ∂μ.map (edgeTranslate a), η ∈ halfPlaneFiniteUnitEvent := by
      rwa [htranslation]
    exact ae_of_ae_map (edgeTranslate_measurable a).aemeasurable hB'
  have hAll : ∀ᵐ ω ∂μ, ∀ a : LatticeVertex, edgeTranslate a ω ∈ halfPlaneFiniteUnitEvent :=
    ae_all_iff.mpr hT
  filter_upwards [hAll] with ω hω
  intro u hu
  obtain ⟨a,ha⟩ := halfPlane_infinite_has_translated_boundary_root ω u hu
  have hb := (mem_halfPlaneFiniteUnitEvent_iff (edgeTranslate a ω)).mp (hω a) 0 (Or.inl rfl)
  exact ha hb

end
end PottsContinuity.PlanarTopology
