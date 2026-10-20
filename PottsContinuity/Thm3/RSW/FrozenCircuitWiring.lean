module

public import PottsContinuity.Thm3.RSW.FrozenCircuitInteriorComparison

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK

/-- Actual open connections in recorded bonds wire the designated circuit
vertices in the pulled-back conditional boundary partition. -/
theorem wiredCircuitPartition_le_frozen_of_recordedConnections
    {X Y : Type*} (H : SimpleGraph Y) (f : X ↪ Y)
    (ξ : BoundaryCondition Y) (K : Configuration H) (B : Set X)
    (hconn : ∀ x ∈ B, ∀ y ∈ B, ActualConnected H K (f x) (f y)) :
    (BoundaryCondition.wired B).partition ≤
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K)).partition := by
  intro x y hxy
  rcases hxy with rfl | ⟨hx,hy⟩
  · exact (frozenBoundary ξ K).partition.refl (f x)
  · exact actualConnected_component H ξ K (hconn x hx y hy)

/-- It suffices to retain actual recorded paths from all designated circuit
vertices to one common vertex. The paths use sampled recorded open bonds. -/
theorem wiredCircuitPartition_le_frozen_of_recordedRootPaths
    {X Y : Type*} (H : SimpleGraph Y) (f : X ↪ Y)
    (ξ : BoundaryCondition Y) (K : Configuration H) (B : Set X) (r : Y)
    (hpath : ∀ x ∈ B, ActualConnected H K (f x) r) :
    (BoundaryCondition.wired B).partition ≤
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K)).partition := by
  apply wiredCircuitPartition_le_frozen_of_recordedConnections H f ξ K B
  intro x hx y hy
  exact (hpath x hx).trans (hpath y hy).symm

end PottsContinuity.RSW
