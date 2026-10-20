module

public import PottsContinuity.BD12.AugmentedUniformTree

/-! Complete reveal trees obtained from literal fresh-edge selection strategies.
Termination follows from the number of coordinates remaining, with no choice
of an unproved continuation and no premature terminal branch. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

theorem remaining_card_insert_lt (R : Finset E) (e : E) (he : e ∉ R) :
    Fintype.card E - (insert e R).card < Fintype.card E - R.card := by
  have h := Finset.card_le_univ (insert e R)
  rw [Finset.card_insert_of_notMem he] at h ⊢
  omega

end
end PottsContinuity.BD12
