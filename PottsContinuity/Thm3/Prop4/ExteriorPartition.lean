module

public import PottsContinuity.PD.FK.ComponentBoundarySupport
public import PottsContinuity.PD.FK.IsolatedBoundaryComponents
public import PottsContinuity.PD.FK.DomainMarkov
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Exact top wiring after a closed-cut exterior exploration

Adapted from FKC/FiniteFK/FrozenBoundaryOutsideRegion.lean. The statement is
parameter independent, but FKC and PD have distinct BoundaryCondition
structures, so its proof is instantiated here on the PD boundary carrier.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK

/-- Open frozen edges entirely outside an embedded region leave exactly the
original wired part inside it. Every original boundary identification is
retained, including identifications via the exterior part of that wired set. -/
theorem pullback_frozen_partition_eq_wired_away {V U : Type*} {G : SimpleGraph V}
    (f : U ↪ V) (D W : Set V) (ξ : BoundaryCondition V) (A : Configuration G)
    (hξ : ξ.boundary ⊆ D ∪ W)
    (hW : (BoundaryCondition.wired W).partition ≤ ξ.partition)
    (hA : ∀ ⦃e : G.edgeSet⦄, e ∈ A → ∀ ⦃u : V⦄, u ∈ e.val → u ∈ D)
    (hf : ∀ u : U, f u ∉ D) :
    (isolatedExtensionPullbackBoundary f (frozenBoundary ξ A)).partition =
      (BoundaryCondition.wired (f ⁻¹' W)).partition := by
  apply Setoid.ext
  intro u v
  change (componentSetoid G ξ A).r (f u) (f v) ↔
    (BoundaryCondition.wired (f ⁻¹' W)).partition.r u v
  constructor
  · intro huv
    have hlarge := componentSetoid_le_wired_union_of_edge_endpoints ξ D A hA huv
    rcases (BoundaryCondition.wired_rel (ξ.boundary ∪ D) (f u) (f v)).mp hlarge with heq | ⟨hu,hv⟩
    · exact (BoundaryCondition.wired_rel _ u v).mpr (Or.inl (f.injective heq))
    · have hfu : f u ∈ W := by
        rcases hu with hu | hu
        · rcases hξ hu with hu | hu
          · exact False.elim (hf u hu)
          · exact hu
        · exact False.elim (hf u hu)
      have hfv : f v ∈ W := by
        rcases hv with hv | hv
        · rcases hξ hv with hv | hv
          · exact False.elim (hf v hv)
          · exact hv
        · exact False.elim (hf v hv)
      exact (BoundaryCondition.wired_rel _ u v).mpr (Or.inr ⟨hfu,hfv⟩)
  · intro huv
    rcases (BoundaryCondition.wired_rel _ u v).mp huv with heq | ⟨hu,hv⟩
    · exact heq ▸ (frozenBoundary ξ A).partition.refl (f u)
    · exact boundary_component G ξ A (hW ((BoundaryCondition.wired_rel W (f u) (f v)).mpr
        (Or.inr ⟨hu,hv⟩)))

end PottsContinuity.Thm3.Prop4
