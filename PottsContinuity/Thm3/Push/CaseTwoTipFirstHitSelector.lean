module

public import PottsContinuity.Thm3.Push.SourceBandArmEvent

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12
noncomputable section
local instance caseTwoTipFirstHitEdgeEq (n : ℕ) :
    DecidableEq (rectangleGraph (0,0) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- Actual retained first-left-hit selector from J=[6s,7s] in the literal
R'=[4s,9s] x [0,2n], sampled in the original source square. -/
def caseTwoTipFirstHitSelector (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n))) :
    Option (SideCollarFirstHitRecord (5*s) (2*n)) :=
  embeddedSideFirstHitSelector (5*s) (2*n) ((2*s:ℕ):ℤ) ((3*s:ℕ):ℤ)
    (rectangleGraph (0,0) (2*n) (2*n))
    (sourceBandEmbedding (2*n) (4*s) (5*s) (2*n) (by omega) le_rfl)
    (sourceBandEmbedding_map_le (2*n) (4*s) (5*s) (2*n) (by omega) le_rfl) C

/-- The exact first-selection success event of the original Case 2 consumer. -/
theorem caseTwoTipFirstHitSelector_isSome_iff (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n))) :
    (caseTwoTipFirstHitSelector n s hfit C).isSome ↔ C ∈ sourceCaseTwoSecondArm n s := by
  have he := embeddedSideFirstHitSelector_isSome_iff (5*s) (2*n) ((2*s:ℕ):ℤ) ((3*s:ℕ):ℤ)
    (by positivity) (by omega) (by omega) (rectangleGraph (0,0) (2*n) (2*n))
    (sourceBandEmbedding (2*n) (4*s) (5*s) (2*n) (by omega) le_rfl)
    (sourceBandEmbedding_map_le (2*n) (4*s) (5*s) (2*n) (by omega) le_rfl) C
  rw [sourceBand_left_arm_iff] at he
  have hl : 4*(s:ℤ)+2*(s:ℤ) = 6*(s:ℤ) := by ring
  have hr : 4*(s:ℤ)+3*(s:ℤ) = 7*(s:ℤ) := by ring
  have hright : 4*(s:ℤ)+5*(s:ℤ) = 9*(s:ℤ) := by ring
  simp only [Nat.cast_mul,Nat.cast_ofNat] at he
  simpa only [caseTwoTipFirstHitSelector,sourceCaseTwoSecondArm,Nat.cast_mul,Nat.cast_ofNat,hl,hr,hright] using he

end
end PottsContinuity.Push
