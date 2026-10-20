module

public import PottsContinuity.Thm3.Push.SquareArmReflection
public import PottsContinuity.Thm3.Push.IsoStoppingReveal
public import PottsContinuity.Thm3.Push.IntervalArmFilledRecord

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.Exploration
noncomputable section
local instance rightArmRecordEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _
local instance rightArmRecordRemainingFintype (N : ℕ)
    (R : Configuration (rectangleGraph (0,0) N N)) :
    Fintype (RemainingConfiguration (rectangleGraph (0,0) N N) R) := Fintype.ofFinite _

/-- Run the filled interval exploration from the RIGHT exterior arc, by
literal reflection of both the original sampled bonds and the source interval. -/
abbrev intervalArmFilledRightReveal (N : ℕ) (l r : ℤ) :=
  isoStoppingReveal (squareArmReflectionIso N)
    (intervalArmFilledLeftReveal N ((N : ℤ)-r) ((N : ℤ)-l))

/-- The right exploration is a stopping record on the full state carrier. -/
theorem intervalArmFilledRightReveal_stable (N : ℕ) (l r : ℤ)
    (A B : Configuration (rectangleGraph (0,0) N N))
    (hstates : B ∩ intervalArmFilledRightReveal N l r A =
      A ∩ intervalArmFilledRightReveal N l r A) :
    intervalArmFilledRightReveal N l r B = intervalArmFilledRightReveal N l r A :=
  isoStoppingReveal_stable _ _ (intervalArmFilledLeftReveal_stable N _ _) A B hstates

/-- Both source success and failure are read by the actual right record. -/
theorem intervalArmEvent_readFromFilledRightReveal
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ)) :
    ReadFromReveal (intervalArmFilledRightReveal N l r) (intervalArmEvent N l r) := by
  have hset : {A | (configurationIso (squareArmReflectionIso N)).symm A ∈
      intervalArmEvent N ((N : ℤ)-r) ((N : ℤ)-l)} = intervalArmEvent N l r := by
    ext A
    have he := (intervalArmEvent_reflection_iff N ((N : ℤ)-r) ((N : ℤ)-l)
      ((configurationIso (squareArmReflectionIso N)).symm A)).symm
    simpa only [Set.mem_ofPred_eq,Equiv.apply_symm_apply,sub_sub_cancel] using he
  rw [← hset]
  exact readFromReveal_isoStoppingReveal _ _ (intervalArmFilledLeftReveal_stable N _ _)
    _ (intervalArmEvent_readFromFilledLeftReveal N _ _ (by omega) (by omega) (by omega))

end
end PottsContinuity.Push
