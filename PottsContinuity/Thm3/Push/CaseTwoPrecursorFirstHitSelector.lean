module

public import PottsContinuity.Thm3.Push.ReflectedSourceBandArmEvent

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12
noncomputable section
local instance caseTwoPrecursorFirstHitEdgeEq (n : ℕ) :
    DecidableEq (rectangleGraph (0,0) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- Actual full precursor from I=[4s,5s] to the first right-side hit
in R=[0,9s] x [0,2n], sampled in the original source square. -/
def caseTwoPrecursorFirstHitSelector (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n))) :
    Option (SideCollarFirstHitRecord (9*s) (2*n)) :=
  embeddedSideFirstHitSelector (9*s) (2*n) ((4*s:ℕ):ℤ) ((5*s:ℕ):ℤ)
    (rectangleGraph (0,0) (2*n) (2*n))
    (reflectedSourceBandEmbedding (2*n) 0 (9*s) (2*n) (by omega) le_rfl)
    (reflectedSourceBandEmbedding_map_le (2*n) 0 (9*s) (2*n) (by omega) le_rfl) C

/-- The exact full-precursor success event of the original Case 2 consumer. -/
theorem caseTwoPrecursorFirstHitSelector_isSome_iff (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n))) :
    (caseTwoPrecursorFirstHitSelector n s hfit C).isSome ↔ C ∈ sourceCaseTwoFirstArm n s := by
  have he := embeddedSideFirstHitSelector_isSome_iff (9*s) (2*n) ((4*s:ℕ):ℤ) ((5*s:ℕ):ℤ)
    (by positivity) (by omega) (by omega) (rectangleGraph (0,0) (2*n) (2*n))
    (reflectedSourceBandEmbedding (2*n) 0 (9*s) (2*n) (by omega) le_rfl)
    (reflectedSourceBandEmbedding_map_le (2*n) 0 (9*s) (2*n) (by omega) le_rfl) C
  rw [reflectedSourceBand_right_arm_iff] at he
  simp only [Nat.cast_zero,Nat.cast_mul,Nat.cast_ofNat,zero_add] at he
  have hl : 9*(s:ℤ)-5*(s:ℤ) = 4*(s:ℤ) := by ring
  have hr : 9*(s:ℤ)-4*(s:ℤ) = 5*(s:ℤ) := by ring
  simpa only [caseTwoPrecursorFirstHitSelector,sourceCaseTwoFirstArm,Nat.cast_mul,Nat.cast_ofNat,hl,hr] using he

end
end PottsContinuity.Push
