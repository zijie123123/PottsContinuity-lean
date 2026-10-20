module

public import PottsContinuity.DualityExt.PositiveBoundaryMerge
public import PottsContinuity.DualityExt.PositiveEndpointDualSubgraphLaw
public import PottsContinuity.DualityExt.PositivePDLawBridge
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.CompletePartialOrder

/-!
# Boundary connectivity criterion for the induced dual partition

The rectangle restriction law produces a boundary partition from the forced
dual edges and the host boundary wiring. This file reduces its identification
with a single wired class to edge-incidence and connectivity statements.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality

noncomputable section

/-- If all forced edges and original boundary vertices lie in `B`, and the
forced-edge connectivity together with the original boundary relation joins
every pair in `B`, then freezing those edges induces exactly wired boundary on
`B`. -/
theorem frozenBoundary_partition_eq_wired_of_boundary_connected
    {V : Type*} {G : SimpleGraph V}
    (ξ : BoundaryCondition V) (R : Configuration G) (B : Set V)
    (hR : ∀ ⦃e : G.edgeSet⦄, e ∈ R → ∀ ⦃u : V⦄, u ∈ e.1 → u ∈ B)
    (hξ : ξ.boundary ⊆ B)
    (hconn : ∀ ⦃u v : V⦄, u ∈ B → v ∈ B →
      (componentSetoid G ξ R).r u v) :
    (frozenBoundary ξ R).partition = (BoundaryCondition.wired B).partition := by
  change componentSetoid G ξ R = (BoundaryCondition.wired B).partition
  apply le_antisymm
  · apply componentSetoid_le
    · intro u v huv
      have hreach : (openGraph G R).reachableSetoid ≤
          (BoundaryCondition.wired B).partition := by
        apply reachableSetoid_le_of_adj (openGraph G R)
          (BoundaryCondition.wired B).partition
        intro x y hxy
        rw [openGraph_adj] at hxy
        rcases hxy with ⟨e, he, hexy⟩
        apply (BoundaryCondition.wired_rel B x y).2
        right
        refine ⟨hR he (by rw [hexy]; exact (Sym2.mem_iff').2 (Or.inl rfl)),
          hR he (by rw [hexy]; exact (Sym2.mem_iff').2 (Or.inr rfl))⟩
      exact hreach huv
    · intro u v huv
      apply (BoundaryCondition.wired_rel B u v).2
      rcases ξ.supported huv with heq | ⟨hu, hv⟩
      · exact Or.inl heq
      · exact Or.inr ⟨hξ hu, hξ hv⟩
  · intro u v huv
    rcases (BoundaryCondition.wired_rel B u v).mp huv with heq | ⟨hu, hv⟩
    · subst v
      exact (componentSetoid G ξ R).refl u
    · exact hconn hu hv

/-- If the frozen edges stay within one of two disjoint classes, the host
partition already refines their separate wiring, and each class is connected
after freezing, then the induced partition is exactly the separately wired
two-block partition. -/
theorem frozenBoundary_partition_eq_twoBlock_of_class_connected
    {V : Type*} {G : SimpleGraph V}
    (ξ : BoundaryCondition V) (R : Configuration G)
    (I O : Set V) (hIO : Disjoint I O)
    (hR : ∀ ⦃e : G.edgeSet⦄, e ∈ R →
      (∀ ⦃u : V⦄, u ∈ e.1 → u ∈ I) ∨
      (∀ ⦃u : V⦄, u ∈ e.1 → u ∈ O))
    (hξ : ξ.partition ≤ (positiveTwoBlockBoundary I O hIO).partition)
    (hI : ∀ ⦃u v : V⦄, u ∈ I → v ∈ I →
      (componentSetoid G ξ R).r u v)
    (hO : ∀ ⦃u v : V⦄, u ∈ O → v ∈ O →
      (componentSetoid G ξ R).r u v) :
    (frozenBoundary ξ R).partition =
      (positiveTwoBlockBoundary I O hIO).partition := by
  change componentSetoid G ξ R =
    (positiveTwoBlockBoundary I O hIO).partition
  apply le_antisymm
  · apply componentSetoid_le
    · intro u v huv
      have hreach : (openGraph G R).reachableSetoid ≤
          (positiveTwoBlockBoundary I O hIO).partition := by
        apply reachableSetoid_le_of_adj (openGraph G R)
          (positiveTwoBlockBoundary I O hIO).partition
        intro x y hxy
        rw [openGraph_adj] at hxy
        rcases hxy with ⟨e, he, hexy⟩
        change (((BoundaryCondition.wired I).partition ⊔
          (BoundaryCondition.wired O).partition).r x y)
        rcases hR he with hIedge | hOedge
        · have hIle : (BoundaryCondition.wired I).partition ≤
              (BoundaryCondition.wired I).partition ⊔
                (BoundaryCondition.wired O).partition := le_sup_left
          apply hIle
          apply (BoundaryCondition.wired_rel I x y).2
          right
          exact ⟨hIedge (by rw [hexy]; exact
            (Sym2.mem_iff').2 (Or.inl rfl)),
            hIedge (by rw [hexy]; exact
            (Sym2.mem_iff').2 (Or.inr rfl))⟩
        · have hOle : (BoundaryCondition.wired O).partition ≤
              (BoundaryCondition.wired I).partition ⊔
                (BoundaryCondition.wired O).partition := le_sup_right
          apply hOle
          apply (BoundaryCondition.wired_rel O x y).2
          right
          exact ⟨hOedge (by rw [hexy]; exact
            (Sym2.mem_iff').2 (Or.inl rfl)),
            hOedge (by rw [hexy]; exact
            (Sym2.mem_iff').2 (Or.inr rfl))⟩
      exact hreach huv
    · exact hξ
  · intro u v huv
    change (((BoundaryCondition.wired I).partition ⊔
      (BoundaryCondition.wired O).partition).r u v) at huv
    have hle : (BoundaryCondition.wired I).partition ⊔
        (BoundaryCondition.wired O).partition ≤ componentSetoid G ξ R := by
      apply sup_le
      · intro x y hxy
        rcases (BoundaryCondition.wired_rel I x y).mp hxy with heq | hIxy
        · subst y
          exact (componentSetoid G ξ R).refl x
        · exact hI hIxy.1 hIxy.2
      · intro x y hxy
        rcases (BoundaryCondition.wired_rel O x y).mp hxy with heq | hOxy
        · subst y
          exact (componentSetoid G ξ R).refl x
        · exact hO hOxy.1 hOxy.2
    exact hle huv

end
end PottsContinuity.DualityExt
