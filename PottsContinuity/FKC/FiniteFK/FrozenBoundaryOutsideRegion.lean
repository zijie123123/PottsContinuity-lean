-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/FrozenBoundaryOutsideRegion.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ClusterBoundaryDomination
public import PottsContinuity.FKC.FiniteFK.IsolatedBoundaryComponents
public import PottsContinuity.FKC.FiniteFK.DomainMarkov
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V U : Type*} {G : SimpleGraph V}

/-- When every frozen open edge lies in a deleted vertex region disjoint from
an embedded domain, its pulled-back frozen partition is exactly the wiring of
the original boundary portion in the retained domain. -/
theorem isolatedExtensionPullback_frozenBoundary_partition_eq_wired_away
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
    have hlarge : (BoundaryCondition.wired (ξ.boundary ∪ D)).partition.r (f u) (f v) :=
      componentSetoid_le_wired_union_of_edge_endpoints ξ D A hA huv
    rcases (BoundaryCondition.wired_rel (ξ.boundary ∪ D) (f u) (f v)).mp hlarge with heq | ⟨hu, hv⟩
    · exact (BoundaryCondition.wired_rel (f ⁻¹' W) u v).mpr (Or.inl (f.injective heq))
    · have hfu : f u ∈ W := by
        rcases hu with hξu | hDu
        · rcases hξ hξu with hDu | hWu
          · exact False.elim ((hf u) hDu)
          · exact hWu
        · exact False.elim ((hf u) hDu)
      have hfv : f v ∈ W := by
        rcases hv with hξv | hDv
        · rcases hξ hξv with hDv | hWv
          · exact False.elim ((hf v) hDv)
          · exact hWv
        · exact False.elim ((hf v) hDv)
      exact (BoundaryCondition.wired_rel (f ⁻¹' W) u v).mpr
        (Or.inr ⟨hfu, hfv⟩)
  · intro huv
    rcases (BoundaryCondition.wired_rel (f ⁻¹' W) u v).mp huv with heq | ⟨hu, hv⟩
    · exact (Setoid.comap_rel f (frozenBoundary ξ A).partition u v).mpr
        (heq ▸ (frozenBoundary ξ A).partition.refl (f u))
    · have hWrel : (BoundaryCondition.wired W).partition.r (f u) (f v) :=
        (BoundaryCondition.wired_rel W (f u) (f v)).mpr
          (Or.inr ⟨hu, hv⟩)
      have hξrel : (frozenBoundary ξ A).partition.r (f u) (f v) := by
        change (componentSetoid G ξ A).r (f u) (f v)
        exact boundary_component G ξ A (hW hWrel)
      exact (Setoid.comap_rel f (frozenBoundary ξ A).partition u v).mpr hξrel

end
end PottsContinuity.FKC.FiniteFK
