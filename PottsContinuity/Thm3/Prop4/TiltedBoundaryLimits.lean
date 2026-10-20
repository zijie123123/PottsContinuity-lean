module

public import PottsContinuity.Thm3.Prop4.TiltedSideCylinders
public import PottsContinuity.Thm3.Prop4.PlaneCylinderCriterion
public import PottsContinuity.Thm3.Prop4.TiltedSelfDual

/-! # Arbitrary admissible lateral partitions share the same tilted weak limit -/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.RCInfinite

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance boundaryLimitEdgeFintype (n M : ℕ) (t : ℝ) :
    Fintype (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _

/-- Actual finite FK law with the specified boundary partition, pushed by the
same literal closed original-edge plane extension as the extreme conventions. -/
def tiltedBoundaryPlaneProbabilityMeasure (θ : Parameters) (n M : ℕ) (t : ℝ)
    (ξ : BoundaryCondition (tiltedWindow n M t : Set (ℤ × ℤ))) :
    ProbabilityMeasure LatticeConfiguration :=
  ⟨((law _ θ ξ).map (tiltedWindowPlaneConfiguration n M t)).toMeasure,
    PMF.toMeasure.isProbabilityMeasure _⟩

/-- Exact original-edge event transport for every admissible or arbitrary
finite boundary partition. -/
theorem tiltedBoundaryPlane_apply (θ : Parameters) (n M : ℕ) (t : ℝ)
    (ξ : BoundaryCondition (tiltedWindow n M t : Set (ℤ × ℤ)))
    (E : Set LatticeConfiguration) (hE : MeasurableSet E) :
    (tiltedBoundaryPlaneProbabilityMeasure θ n M t ξ).toMeasure E =
      measure (finiteLatticeGraph (tiltedWindow n M t)) θ ξ
        {A | tiltedWindowPlaneConfiguration n M t A ∈ E} := by
  change ((law _ θ ξ).map (tiltedWindowPlaneConfiguration n M t)).toMeasure E = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hE]
  rfl

/-- Actual all-open cylinders under the arbitrary-partition finite law. -/
theorem tiltedBoundaryPlane_allOpen_eq (θ : Parameters) (n M : ℕ) (t : ℝ)
    (ξ : BoundaryCondition (tiltedWindow n M t : Set (ℤ × ℤ))) (F : Finset squareLattice.edgeSet) :
    (tiltedBoundaryPlaneProbabilityMeasure θ n M t ξ).toMeasure.real (LatticeConfiguration.allOpen F) =
      (measure (finiteLatticeGraph (tiltedWindow n M t)) θ ξ
        (finiteSubgraphOpenEvent (tiltedWindow n M t) F)).toReal := by
  unfold Measure.real
  rw [tiltedBoundaryPlane_apply θ n M t ξ _ (LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet]
  congr 2
  ext A
  simp only [tiltedWindowPlaneConfiguration,LatticeConfiguration.allOpen,finiteSubgraphOpenEvent,
    Set.mem_ofPred_eq,decide_eq_true_eq]
  rfl

/-- Every sequence of boundary partitions between the two lateral extremes
converges to the same genuine top-only weak limit. -/
theorem tiltedBoundaryPlane_tendsto_of_partition_bounds (θ : Parameters) (n : ℕ) (t : ℝ) (ht : |t| ≤ 1)
    (ξ : ∀ M : ℕ, BoundaryCondition (tiltedWindow n M t : Set (ℤ × ℤ)))
    (hlo : ∀ M, (tiltedWindowBoundary n M t 0).partition ≤ (ξ M).partition)
    (hhi : ∀ M, (ξ M).partition ≤ (tiltedWindowBoundary n M t 1).partition)
    (ν : ProbabilityMeasure LatticeConfiguration)
    (hν : Tendsto (tiltedWindowPlaneProbabilityMeasure θ n t 0) atTop (𝓝 ν)) :
    Tendsto (fun M => tiltedBoundaryPlaneProbabilityMeasure θ n M t (ξ M)) atTop (𝓝 ν) := by
  apply plane_tendsto_of_allOpen_real
  intro F
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tilted_top_allOpen_real_tendsto θ n t ν hν F)
    (tilted_side_allOpen_real_tendsto θ n t ht ν hν 1 F)
  · intro M
    dsimp only
    rw [tiltedWindowPlane_allOpen_eq θ n M t 0 F,tiltedBoundaryPlane_allOpen_eq θ n M t (ξ M) F]
    apply measure_boundary_comparison θ _ _ (hlo M)
    intro A B hAB hA
    exact hA.trans (Finset.map_subset_map.mpr hAB)
  · intro M
    dsimp only
    rw [tiltedBoundaryPlane_allOpen_eq θ n M t (ξ M) F,tiltedWindowPlane_allOpen_eq θ n M t 1 F]
    apply measure_boundary_comparison θ _ _ (hhi M)
    intro A B hAB hA
    exact hA.trans (Finset.map_subset_map.mpr hAB)

/-- Supported side partitions are automatically below wiring the full top and
artificial sides. Their identifications may otherwise be completely arbitrary. -/
theorem lateral_partition_le_topSides (n M : ℕ) (t : ℝ)
    (ξ : BoundaryCondition (tiltedWindow n M t : Set (ℤ × ℤ)))
    (hξ : ξ.boundary ⊆ tiltedWindowWiredVertices n M t 1) :
    ξ.partition ≤ (tiltedWindowBoundary n M t 1).partition := by
  intro u v huv
  change u = v ∨ u ∈ tiltedWindowWiredVertices n M t 1 ∧ v ∈ tiltedWindowWiredVertices n M t 1
  rcases ξ.supported huv with heq | ⟨hu,hv⟩
  · exact Or.inl heq
  · exact Or.inr ⟨hξ hu,hξ hv⟩

/-- Arbitrary lateral boundary conditions, retaining top wiring and free
bottom, have the same weak limit. This is the full lateral-independence form. -/
theorem tiltedBoundaryPlane_tendsto (θ : Parameters) (n : ℕ) (t : ℝ) (ht : |t| ≤ 1)
    (ξ : ∀ M : ℕ, BoundaryCondition (tiltedWindow n M t : Set (ℤ × ℤ)))
    (htop : ∀ M, (tiltedWindowBoundary n M t 0).partition ≤ (ξ M).partition)
    (hlateral : ∀ M, (ξ M).boundary ⊆ tiltedWindowWiredVertices n M t 1)
    (ν : ProbabilityMeasure LatticeConfiguration)
    (hν : Tendsto (tiltedWindowPlaneProbabilityMeasure θ n t 0) atTop (𝓝 ν)) :
    Tendsto (fun M => tiltedBoundaryPlaneProbabilityMeasure θ n M t (ξ M)) atTop (𝓝 ν) :=
  tiltedBoundaryPlane_tendsto_of_partition_bounds θ n t ht ξ htop
    (fun M => lateral_partition_le_topSides n M t (ξ M) (hlateral M)) ν hν

end

end PottsContinuity.Thm3.Prop4
