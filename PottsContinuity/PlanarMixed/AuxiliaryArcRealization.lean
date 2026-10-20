module

public import PottsContinuity.PlanarMixed.InducedEndpointMixedBound
public import PottsContinuity.PlanarMixed.CrosscutOpenWalks
public import PottsContinuity.PlanarMixed.OmegaInterfaces
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import PottsContinuity.DualityExt.PositiveConnectedBoundaryPartition

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK PD.Duality DualityExt BD12
noncomputable section

/-- Two disjoint classes of actual auxiliary open bonds realize the separate
source boundary exactly. Connections through the host retain their full
partition before restriction to the source vertices. -/
theorem auxiliaryArc_source_partition_eq
    {V : Type*} [Finite V] {a : LatticeVertex} {w h : ℕ} {G : SimpleGraph V}
    (f : V ↪ RectangleVertex a w h)
    (A C : Set V) (hAC : Disjoint A C)
    (H : RemovedConfiguration (rectangleGraph a w h)
      (subgraphRemovedEdges (G.map f) (rectangleGraph a w h)))
    (hR : ∀ ⦃e : (rectangleGraph a w h).edgeSet⦄, e ∈ H.val →
      (∀ ⦃z : RectangleVertex a w h⦄, z ∈ e.val → z ∈ f '' A) ∨
      (∀ ⦃z : RectangleVertex a w h⦄, z ∈ e.val → z ∈ f '' C))
    (hA : ∀ u ∈ A, ∀ v ∈ A, ActualConnected (rectangleGraph a w h) H.val (f u) (f v))
    (hC : ∀ u ∈ C, ∀ v ∈ C, ActualConnected (rectangleGraph a w h) H.val (f u) (f v)) :
    (twoBlockBoundary A C hAC).partition =
      (isolatedExtensionPullbackBoundary f
        (frozenBoundary (BoundaryCondition.free ∅) H.val)).partition := by
  have hdis : Disjoint (f '' A) (f '' C) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨u, hu, he⟩ ⟨v, hv, he'⟩
    have huv : u = v := f.injective (he.trans he'.symm)
    exact Set.disjoint_left.mp hAC hu (huv.symm ▸ hv)
  have hfull := frozenBoundary_partition_eq_twoBlock_of_class_connected
    (BoundaryCondition.free ∅) H.val (f '' A) (f '' C) hdis hR bot_le
    (by
      rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
      exact actualConnected_component _ _ _ (hA u hu v hv))
    (by
      rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
      exact actualConnected_component _ _ _ (hC u hu v hv))
  apply Setoid.ext
  intro u v
  change (twoBlockBoundary A C hAC).partition.r u v ↔
    (frozenBoundary (BoundaryCondition.free ∅) H.val).partition.r (f u) (f v)
  rw [hfull]
  change (twoBlockBoundary A C hAC).partition.r u v ↔
    (twoBlockBoundary (f '' A) (f '' C) hdis).partition.r (f u) (f v)
  rw [twoBlockBoundary_partition_rel, twoBlockBoundary_partition_rel]
  simp only [Set.mem_image, f.injective.eq_iff, exists_eq_right]

section Bound
variable {V : Type*} [Finite V] {a : LatticeVertex} {w h : ℕ}
  (G : SimpleGraph V) (f : V ↪ RectangleVertex a w h)
  (hG : G.map f ≤ rectangleGraph a w h)
local notation "D" => positiveActiveGraph (rectangleSubgraphDualGraph hG)
local notation "ι" => positiveActiveInclusion (rectangleSubgraphDualGraph hG)
local notation "d" => inducedEndpointDualCarrierIso f hG

end Bound

end
end PottsContinuity.PlanarMixed
