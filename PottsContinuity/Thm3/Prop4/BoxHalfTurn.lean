module

public import PottsContinuity.Thm3.Prop4.TubeHalfTurn
public import PottsContinuity.Thm3.RSW.FiniteIso

/-! # The actual original-box half-turn preserves the free FK law -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
noncomputable section

/-- Rotate the actual square by 180 degrees about its original center. -/
def boxHalfTurnIso (n : ℕ) :
    (squareLattice.induce (box n : Set (ℤ × ℤ))) ≃g
      squareLattice.induce (box n : Set (ℤ × ℤ)) where
  toEquiv :=
    { toFun := fun z => ⟨-z.val,(mem_box_neg_iff n z.val).mpr z.property⟩
      invFun := fun z => ⟨-z.val,(mem_box_neg_iff n z.val).mpr z.property⟩
      left_inv := by intro z; apply Subtype.ext; exact neg_neg z.val
      right_inv := by intro z; apply Subtype.ext; exact neg_neg z.val }
  map_rel_iff' := by
    intro a b
    change |(-a.val.1)-(-b.val.1)|+|(-a.val.2)-(-b.val.2)|=1 ↔
      |a.val.1-b.val.1|+|a.val.2-b.val.2|=1
    rw [neg_sub_neg,neg_sub_neg,abs_sub_comm b.val.1 a.val.1,abs_sub_comm b.val.2 a.val.2]

@[simp] theorem boxHalfTurnIso_val (n : ℕ) (z : (box n : Set (ℤ × ℤ))) :
    (boxHalfTurnIso n z).val = -z.val := rfl

/-- Arbitrary event probabilities, including mixed increasing/decreasing path
conditions, transport by the exact finite graph isomorphism. -/
theorem boxHalfTurn_free_event_probability (θ : PD.FK.Parameters) (n : ℕ)
    (E : Set (PD.FK.Configuration (squareLattice.induce (box n : Set (ℤ × ℤ))))) :
    (PD.FK.measure (squareLattice.induce (box n : Set (ℤ × ℤ))) θ
      (PD.FK.BoundaryCondition.free ∅) E).toReal =
    (PD.FK.measure (squareLattice.induce (box n : Set (ℤ × ℤ))) θ
      (PD.FK.BoundaryCondition.free ∅)
      {A | PD.FK.configurationIso (boxHalfTurnIso n) A ∈ E}).toReal :=
  RSW.free_probability_iso θ (boxHalfTurnIso n) E

end
end PottsContinuity.Thm3.Prop4
