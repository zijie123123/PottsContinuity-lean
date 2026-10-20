module

public import PottsContinuity.Thm3.Prop4.TiltedTwoCutReveal

/-! # The complete record fixes success and the surviving interval -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

noncomputable section

local instance recordSuccessEdgeFintype (n M : ℕ) (t : ℝ) :
    Fintype (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _
local instance recordSuccessEdgeDecidableEq (n M : ℕ) (t : ℝ) :
    DecidableEq (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Classical.decEq _

private theorem restrict_agreement {E : Type*} [DecidableEq E]
    (A B R T : Finset E) (hT : T ⊆ R) (h : B ∩ R = A ∩ R) : B ∩ T = A ∩ T := by
  have h' := congrArg (fun S : Finset E => S ∩ T) h
  simpa only [Finset.inter_assoc,Finset.inter_eq_right.mpr hT] using h'

/-- The random interval itself, not just its revealed edge set, is fixed by
agreement on the complete recorded states. -/
theorem tiltedTwoCutBounds_eq_of_reveal_agree (n M : ℕ) (t : ℝ) (a b : ℤ) (K : ℕ)
    (A B : PD.FK.Configuration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))))
    (h : B ∩ tiltedTwoCutReveal n M t a b K A = A ∩ tiltedTwoCutReveal n M t a b K A) :
    tiltedTwoCutBounds n M t a b K B = tiltedTwoCutBounds n M t a b K A := by
  have hsub := Finset.union_subset_iff.mp (tiltedCutScans_tested_subset_reveal n M t a b K A)
  have hL := tiltedCutScan_eq_of_agree n M t (fun i => a+i) K A B
    (restrict_agreement A B _ _ hsub.1 h)
  have hR := tiltedCutScan_eq_of_agree n M t (fun i => b-i) K A B
    (restrict_agreement A B _ _ hsub.2 h)
  unfold tiltedTwoCutBounds
  rw [hL,hR]

/-- Every state on the actual stopping record has the same success status
and the same selected integer interval. -/
theorem tiltedTwoCutBounds_eq_on_record (n M : ℕ) (t : ℝ) (a b : ℤ) (K : ℕ)
    (A B : PD.FK.Configuration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))))
    (hB : B ∈ Exploration.revealRecordEvent (tiltedTwoCutReveal n M t a b K) A) :
    tiltedTwoCutBounds n M t a b K B = tiltedTwoCutBounds n M t a b K A :=
  tiltedTwoCutBounds_eq_of_reveal_agree n M t a b K A B hB.2

end

end PottsContinuity.Thm3.Prop4
