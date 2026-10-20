module

public import PottsContinuity.Thm3.Push.IntervalArmFilledForest
public import PottsContinuity.Thm3.Push.SquareRegionFrontierWitness
public import PottsContinuity.Thm3.Push.IntervalArmRecord

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.Exploration
noncomputable section
local instance intervalFilledRecordEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _
local instance intervalFilledRecordRemainingFintype (N : ℕ)
    (R : Configuration (rectangleGraph (0,0) N N)) :
    Fintype (RemainingConfiguration (rectangleGraph (0,0) N N) R) := Fintype.ofFinite _

/-- Filling the source exploration retains an actual arm from the original
bottom interval to the full top side. No path containment premise is assumed. -/
theorem intervalArmFilledLeftFrontier_contains_arm
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N))
    {s t : RectangleVertex (0,0) N N} (p : (openGraph (rectangleGraph (0,0) N N) A).Walk s t)
    (hs : s.val.2 = 0) (ht : t.val.2 = (N : ℤ)) (hsl : l ≤ s.val.1) (hsr : s.val.1 ≤ r) :
    ∃ u v : RectangleVertex (0,0) N N,
      u.val.2 = 0 ∧ l ≤ u.val.1 ∧ u.val.1 ≤ r ∧ v.val.2 = (N : ℤ) ∧
      ActualConnected (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A) u v := by
  have hF : squareRegionFrontier N (intervalArmRightRegion N l r A)ᶜ =
      intervalArmFilledLeftFrontier N l r A := by
    unfold squareRegionFrontier intervalArmFilledLeftFrontier
    congr 1
    funext v
    exact decide_eq_decide.mpr Iff.rfl
  simpa only [hF] using
    (squareRegionFrontier_contains_interval_arm N l r hl hlr hr (intervalArmRightRegion N l r A)ᶜ
    (fun v hv hright => (outsideSeedRegion_subset_compl _ _ _ hright)
      (intervalArmLeftReached_contains_seed N l A hv))
    (fun v hv hnot => hnot
      (intervalArmRightRegion_contains_seed_of_arm N l r hl hlr hr A p hs ht hsl hsr hv)))

/-- Source arm success and failure are read from the complete filled record. -/
theorem intervalArmEvent_readFromFilledLeftReveal
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ)) :
    ReadFromReveal (intervalArmFilledLeftReveal N l r) (intervalArmEvent N l r) := by
  intro A B hB
  have hsmall := recorded_agreement_of_subset A B _ _ (intervalArmLeftReveal_subset_filled N l r A) hB.2
  exact intervalArmEvent_readFromLeftReveal N l r hl hlr hr A B
    ⟨intervalArmLeftReveal_stable N l A B hsmall,hsmall⟩

end
end PottsContinuity.Push
