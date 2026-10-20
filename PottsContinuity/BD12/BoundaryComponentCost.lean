module

public import PottsContinuity.PD.FK.BoundaryComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.CompletePartialOrder

/-! Boundary wiring changes the number of components by at most the number
of boundary vertices, uniformly over all actual edge configurations. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK
noncomputable section
open scoped Classical

variable {V : Type*} [Finite V] (G : SimpleGraph V)

/-- Singleton vertices outside the designated boundary give distinct classes. -/
theorem boundary_partition_card_lower_bound (ξ : BoundaryCondition V) :
    Nat.card V ≤ Nat.card (Quotient ξ.partition) + Nat.card ξ.boundary := by
  let f : ↥(ξ.boundaryᶜ) → Quotient ξ.partition := fun v => Quotient.mk _ v.val
  have hf : Function.Injective f := by
    intro x y hxy
    have hrel : ξ.partition.r x.val y.val := Quotient.exact hxy
    rcases ξ.supported hrel with h | h
    · exact Subtype.ext h
    · exact False.elim (x.property h.1)
  have h := Nat.card_le_card_of_injective f hf
  let : Fintype V := Fintype.ofFinite V
  let : Fintype ξ.boundary := Fintype.ofFinite _
  let : Fintype ↥(ξ.boundaryᶜ) := Fintype.ofFinite _
  have hcard : Nat.card ↥(ξ.boundaryᶜ) + Nat.card ξ.boundary = Nat.card V := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_compl_set]
    exact Nat.sub_add_cancel (Fintype.card_subtype_le _)
  omega

/-- Every boundary identification can only merge actual open components. -/
theorem componentCount_boundary_le_free (ξ : BoundaryCondition V) (A : Configuration G) :
    componentCount G ξ A ≤ componentCount G (BoundaryCondition.free ξ.boundary) A := by
  have hle : componentSetoid G (BoundaryCondition.free ξ.boundary) A ≤
      componentSetoid G ξ A := by
    simp only [componentSetoid_free]
    exact le_sup_left
  let f := Setoid.map_of_le hle
  have hf : Function.Surjective f := by
    intro c
    refine Quotient.inductionOn c ?_
    intro v
    exact ⟨Quotient.mk _ v, rfl⟩
  exact Nat.card_le_card_of_surjective f hf

/-- The loss of components is bounded by boundary size, for every supported
partition and every configuration, including an empty boundary or graph. -/
theorem componentCount_free_le_boundary_add (ξ : BoundaryCondition V) (A : Configuration G) :
    componentCount G (BoundaryCondition.free ξ.boundary) A ≤
      componentCount G ξ A + Nat.card ξ.boundary := by
  have hi := componentCount_union_increment_mono_boundary (G := G)
    (BoundaryCondition.free ξ.boundary) ξ bot_le ∅ ∅ (by simp) A
  simp only [Finset.empty_union] at hi
  rw [componentCount_free_empty, componentCount_empty] at hi
  have hc := boundary_partition_card_lower_bound ξ
  omega

end
end PottsContinuity.BD12
