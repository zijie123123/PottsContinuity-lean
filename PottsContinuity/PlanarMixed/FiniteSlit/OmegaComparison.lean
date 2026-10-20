module

public import PottsContinuity.PlanarMixed.FiniteSlit.Comparison
public import PottsContinuity.PD.FK.EmbeddedBoundaryUpper

/-! The finite Omega comparison from its two deterministic geometry facts.
The exterior DMP mixture and every probability comparison are proved here. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12 MeasureTheory
noncomputable section

/-- Deterministic segment restriction plus the exact exterior partition
bound imply the finite reference-to-Omega comparison, uniformly in the exterior. -/
theorem omega_connection_probability_ge_reference_of_geometry
    (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ))
    {W : Type*} [Finite W] (H : SimpleGraph W)
    (i : W ↪ Vertex M x) (hH : H.map i ≤ graph M x y)
    (G1 G2 : Set W) (hdis : Disjoint G1 G2)
    (q : Set.Ici (1 : ℝ))
    (hpaths : ∀ C ∈ connectionEvent M x y,
      embeddedConfigurationRestriction H (graph M x y) i hH C ∈
        arcsConnectionEvent H G1 G2)
    (hpart : ∀ K : RemovedConfiguration (graph M x y)
        (subgraphRemovedEdges (H.map i) (graph M x y)),
      (isolatedExtensionPullbackBoundary i
        (frozenBoundary (boundary M x y hM hy hyM) K.val)).partition ≤
          (twoBlockBoundary G1 G2 hdis).partition) :
    (measure (graph M x y) (criticalParameters q) (boundary M x y hM hy hyM)
      (connectionEvent M x y)).toReal ≤
      (measure H (criticalParameters q) (twoBlockBoundary G1 G2 hdis)
        (arcsConnectionEvent H G1 G2)).toReal := by
  have hmono := ENNReal.toReal_mono
    (measure_ne_top (measure (graph M x y) (criticalParameters q) (boundary M x y hM hy hyM)) _)
    (measure_mono hpaths)
  exact hmono.trans
    (embeddedConfigurationRestriction_preimage_measure_le_of_frozen_partition
      H (graph M x y) i hH (criticalParameters q) (boundary M x y hM hy hyM)
      (twoBlockBoundary G1 G2 hdis) (arcsConnectionEvent H G1 G2)
      (arcsConnectionEvent_isUpperSet G1 G2) hpart)

/-- The numerical Case 2 Omega bound from a uniform finite reference bound.
Reference duality and actual crosscut geometry remain explicitly separate. -/
theorem omega_connection_lower_bound_of_referenceBound_and_geometry
    (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ))
    {W : Type*} [Finite W] (H : SimpleGraph W)
    (i : W ↪ Vertex M x) (hH : H.map i ≤ graph M x y)
    (G1 G2 : Set W) (hdis : Disjoint G1 G2)
    (q : Set.Ici (1 : ℝ)) (η : BoundaryCondition W)
    (hη : (twoBlockBoundary G1 G2 hdis).partition ≤ η.partition)
    (hreference : 1/(1+(q : ℝ)^2) ≤
      (measure (graph M x y) (criticalParameters q) (boundary M x y hM hy hyM)
        (connectionEvent M x y)).toReal)
    (hpaths : ∀ C ∈ connectionEvent M x y,
      embeddedConfigurationRestriction H (graph M x y) i hH C ∈
        arcsConnectionEvent H G1 G2)
    (hpart : ∀ K : RemovedConfiguration (graph M x y)
        (subgraphRemovedEdges (H.map i) (graph M x y)),
      (isolatedExtensionPullbackBoundary i
        (frozenBoundary (boundary M x y hM hy hyM) K.val)).partition ≤
          (twoBlockBoundary G1 G2 hdis).partition) :
    1/(1+(q : ℝ)^2) ≤
      (measure H (criticalParameters q) η (arcsConnectionEvent H G1 G2)).toReal := by
  exact hreference.trans
    ((omega_connection_probability_ge_reference_of_geometry M x y hM hy hyM H i hH
      G1 G2 hdis q hpaths hpart).trans
        (measure_boundary_comparison (criticalParameters q) (twoBlockBoundary G1 G2 hdis) η
          hη (arcsConnectionEvent H G1 G2) (arcsConnectionEvent_isUpperSet G1 G2)))

end
end PottsContinuity.PlanarMixed.FiniteSlit
