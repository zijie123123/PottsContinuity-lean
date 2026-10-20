module

public import PottsContinuity.PlanarMixed.FiniteSlit.FirstContactCrop

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
noncomputable section

/-- The unique first-contact index of a walk that visits the specified set.
The existence premise is explicit; no value is assigned to a non-hitting walk. -/
def firstContactIndex {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (target : Set V)
    (hhit : ∃ k, k ≤ p.length ∧ p.getVert k ∈ target) : ℕ := by
  classical
  exact Nat.find hhit

/-- Least-index selection has the exact first-contact characterization. -/
theorem isFirstContact_firstContactIndex {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (target : Set V)
    (hhit : ∃ k, k ≤ p.length ∧ p.getVert k ∈ target) :
    IsFirstContact p target (firstContactIndex p target hhit) := by
  classical
  have hk := Nat.find_spec hhit
  refine ⟨hk.1,hk.2,?_⟩
  intro j hj hmem
  have hjle := Nat.find_min' hhit (show j ≤ p.length ∧ p.getVert j ∈ target from
    ⟨by change j < Nat.find hhit at hj; omega,hmem⟩)
  change j < Nat.find hhit at hj
  omega

end
end PottsContinuity.PlanarMixed.FiniteSlit
