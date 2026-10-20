module

public import PottsContinuity.Thm3.Push.IntervalArmRightRecord

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance rightArmFrontierEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _

/-- Original primal frontier bonds of the reflected filled exploration. -/
abbrev intervalArmFilledRightFrontier (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) :=
  configurationIso (squareArmReflectionIso N)
    (intervalArmFilledLeftFrontier N ((N : ℤ)-r) ((N : ℤ)-l)
      ((configurationIso (squareArmReflectionIso N)).symm A))

/-- The right frontier consists of actual OPEN bonds in its own full record. -/
theorem intervalArmFilledRightFrontier_subset_open_record
    (N : ℕ) (l r : ℤ) (A : Configuration (rectangleGraph (0,0) N N)) :
    intervalArmFilledRightFrontier N l r A ⊆ A ∩ intervalArmFilledRightReveal N l r A := by
  let B := (configurationIso (squareArmReflectionIso N)).symm A
  have hs := (intervalArmFilledLeftFrontier_subset_open_raw_record N ((N : ℤ)-r) ((N : ℤ)-l) B).trans
    (Finset.inter_subset_inter_left (intervalArmLeftReveal_subset_filled N ((N : ℤ)-r) ((N : ℤ)-l) B))
  have hc : configurationIso (squareArmReflectionIso N)
      (intervalArmFilledLeftFrontier N ((N : ℤ)-r) ((N : ℤ)-l) B) ⊆
      configurationIso (squareArmReflectionIso N)
        (B ∩ intervalArmFilledLeftReveal N ((N : ℤ)-r) ((N : ℤ)-l) B) :=
    Finset.map_subset_map.mpr hs
  rw [configurationIso_inter] at hc
  simpa only [B,Equiv.apply_symm_apply,intervalArmFilledRightFrontier,
    intervalArmFilledRightReveal,isoStoppingReveal] using hc

/-- Actual source success yields an arm in the original right frontier,
with the original interval and the entire top side preserved. -/
theorem intervalArmEvent_on_right_filled_frontier
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N)) (hA : A ∈ intervalArmEvent N l r) :
    intervalArmFilledRightFrontier N l r A ∈ intervalArmEvent N l r := by
  let B := (configurationIso (squareArmReflectionIso N)).symm A
  have he := intervalArmEvent_reflection_iff N ((N : ℤ)-r) ((N : ℤ)-l) B
  have hB : B ∈ intervalArmEvent N ((N : ℤ)-r) ((N : ℤ)-l) := by
    apply he.mp
    simpa only [B,Equiv.apply_symm_apply,sub_sub_cancel] using hA
  obtain ⟨s,hs,t,ht,⟨p⟩⟩ := hB
  obtain ⟨u,v,hu,hul,hur,hv,huv⟩ := intervalArmFilledLeftFrontier_contains_arm
    N ((N : ℤ)-r) ((N : ℤ)-l) (by omega) (by omega) (by omega)
      B p hs.1 ht hs.2.1 hs.2.2
  have hF : intervalArmFilledLeftFrontier N ((N : ℤ)-r) ((N : ℤ)-l) B ∈
      intervalArmEvent N ((N : ℤ)-r) ((N : ℤ)-l) := ⟨u,⟨hu,hul,hur⟩,v,hv,huv⟩
  have hreflect := (intervalArmEvent_reflection_iff N ((N : ℤ)-r) ((N : ℤ)-l) _).mpr hF
  simpa only [sub_sub_cancel] using hreflect

end
end PottsContinuity.Push
