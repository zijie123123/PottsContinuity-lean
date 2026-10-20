module

public import PottsContinuity.Thm3.Push.IntervalArmRightFrontier

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section
local instance rawRightDeterminationEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _

/-- The unfilled right dual-cluster queries, transported by reflection. -/
def intervalArmRawRightReveal (N : ℕ) (r : ℤ) :=
  isoStoppingReveal (squareArmReflectionIso N)
    (intervalArmLeftReveal N ((N : ℤ)-r))

/-- Filling is determined by the raw queries; states of filled holes need
not be supplied to determine the resulting query shape. -/
theorem intervalArmFilledRightReveal_eq_of_raw_agreement (N : ℕ) (l r : ℤ)
    (A B : Configuration (rectangleGraph (0,0) N N))
    (hstates : B ∩ intervalArmRawRightReveal N r A =
      A ∩ intervalArmRawRightReveal N r A) :
    intervalArmFilledRightReveal N l r B = intervalArmFilledRightReveal N l r A := by
  have hraw := isoStoppingReveal_agreement_pullback (squareArmReflectionIso N)
    (intervalArmLeftReveal N ((N : ℤ)-r)) A B (by simpa only [intervalArmRawRightReveal, Finset.ext_iff, Finset.mem_inter] using hstates)
  have hregion := intervalArmRightRegion_eq_of_raw_record_agreement N
    ((N : ℤ)-r) ((N : ℤ)-l) _ _
    (by simpa only [Finset.ext_iff, Finset.mem_inter] using hraw)
  unfold intervalArmFilledRightReveal isoStoppingReveal intervalArmFilledLeftReveal
  rw [hregion]

/-- Raw queried states also determine the whole filled primal frontier. -/
theorem intervalArmFilledRightFrontier_eq_of_raw_agreement (N : ℕ) (l r : ℤ)
    (A B : Configuration (rectangleGraph (0,0) N N))
    (hstates : B ∩ intervalArmRawRightReveal N r A =
      A ∩ intervalArmRawRightReveal N r A) :
    intervalArmFilledRightFrontier N l r B = intervalArmFilledRightFrontier N l r A := by
  have hraw := isoStoppingReveal_agreement_pullback (squareArmReflectionIso N)
    (intervalArmLeftReveal N ((N : ℤ)-r)) A B (by simpa only [intervalArmRawRightReveal, Finset.ext_iff, Finset.mem_inter] using hstates)
  have hregion := intervalArmRightRegion_eq_of_raw_record_agreement N
    ((N : ℤ)-r) ((N : ℤ)-l) _ _
    (by simpa only [Finset.ext_iff, Finset.mem_inter] using hraw)
  unfold intervalArmFilledRightFrontier intervalArmFilledLeftFrontier
  rw [hregion]

end
end PottsContinuity.Push
