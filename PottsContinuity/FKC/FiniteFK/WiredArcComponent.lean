-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/WiredArcComponent.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.Graph

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

private theorem wiredArc_actualConnected_symm {V : Type*} {G : SimpleGraph V}
    {A : Configuration G} {u v : V} (h : ActualConnected G A u v) :
    ActualConnected G A v u := h.symm

private theorem wiredArc_actualConnected_trans {V : Type*} {G : SimpleGraph V}
    {A : Configuration G} {u v w : V} (h₁ : ActualConnected G A u v)
    (h₂ : ActualConnected G A v w) : ActualConnected G A u w := h₁.trans h₂

/-- In a wired component, a vertex belongs to the component of any specified
vertex of the wired set exactly when its actual open cluster hits that set. -/
theorem wired_componentSetoid_rel_iff_exists_actualConnected
    {V : Type*} (G : SimpleGraph V) (A : Configuration G) (S : Set V)
    {u v : V} (hv : v ∈ S) :
    (componentSetoid G (BoundaryCondition.wired S) A).r u v ↔
      ∃ w ∈ S, ActualConnected G A u w := by
  classical
  let hit : V → Prop := fun x => ∃ w ∈ S, ActualConnected G A x w
  have hit_forward {x y : V} (hxy : ActualConnected G A x y) (hy : hit y) : hit x := by
    obtain ⟨w, hw, hyw⟩ := hy
    exact ⟨w, hw, wiredArc_actualConnected_trans hxy hyw⟩
  have hit_backward {x y : V} (hxy : ActualConnected G A x y) (hx : hit x) : hit y := by
    exact hit_forward (wiredArc_actualConnected_symm hxy) hx
  let R : Setoid V :=
    { r := fun x y => ActualConnected G A x y ∨ (hit x ∧ hit y)
      iseqv :=
        { refl := fun x => Or.inl (SimpleGraph.Reachable.refl x)
          symm := by
            intro x y h
            rcases h with h | ⟨hx, hy⟩
            · exact Or.inl (wiredArc_actualConnected_symm h)
            · exact Or.inr ⟨hy, hx⟩
          trans := by
            intro x y z hxy hyz
            rcases hxy with hxy | ⟨hx, hy⟩
            · rcases hyz with hyz | ⟨hy', hz⟩
              · exact Or.inl (wiredArc_actualConnected_trans hxy hyz)
              · exact Or.inr ⟨hit_forward hxy hy', hz⟩
            · rcases hyz with hyz | ⟨hy', hz⟩
              · exact Or.inr ⟨hx, hit_backward hyz hy⟩
              · exact Or.inr ⟨hx, hz⟩ } }
  constructor
  · intro hrel
    have hsub : componentSetoid G (BoundaryCondition.wired S) A ≤ R := by
      apply componentSetoid_le G (BoundaryCondition.wired S) A R
      · intro x y hconn
        exact Or.inl hconn
      · intro x y hwire
        rcases (BoundaryCondition.wired_rel S x y).mp hwire with hxy | ⟨hx, hy⟩
        · subst y
          exact Or.inl (SimpleGraph.Reachable.refl x)
        · exact Or.inr ⟨⟨x, hx, SimpleGraph.Reachable.refl x⟩,
            ⟨y, hy, SimpleGraph.Reachable.refl y⟩⟩
    have hR := hsub hrel
    rcases hR with hconn | ⟨hu, _⟩
    · exact ⟨v, hv, hconn⟩
    · exact hu
  · rintro ⟨w, hw, huw⟩
    exact Setoid.trans' (componentSetoid G (BoundaryCondition.wired S) A)
      (actualConnected_component G (BoundaryCondition.wired S) A huw)
      (boundary_component G (BoundaryCondition.wired S) A
        ((BoundaryCondition.wired_rel S w v).mpr (Or.inr ⟨hw, hv⟩)))

end PottsContinuity.FKC.FiniteFK
