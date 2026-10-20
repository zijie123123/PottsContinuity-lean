module

public import PottsContinuity.Thm3.Push.SquareRegionLeafBoundary
public import PottsContinuity.Thm3.Push.IntervalArmFilledActiveLocality
public import PottsContinuity.Thm3.Push.IntervalArmFilledRecord

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- Actual source success supplies the literal left/right exterior seed
labels of the filled face region. The left statement is also valid off it. -/
theorem intervalArmFilled_region_seed_labels
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N)) (hA : A ∈ intervalArmEvent N l r) :
    (∀ b ∈ intervalArmLeftDualPorts N l, b ∈ (intervalArmRightRegion N l r A)ᶜ) ∧
      (∀ b ∈ intervalArmRightDualPorts N r, b ∉ (intervalArmRightRegion N l r A)ᶜ) := by
  obtain ⟨s,hs,t,ht,⟨p⟩⟩ := hA
  constructor
  · intro b hb hR
    exact (outsideSeedRegion_subset_compl _ _ _ hR) (intervalArmLeftReached_contains_seed N l A hb)
  · intro b hb hnot
    exact hnot (intervalArmRightRegion_contains_seed_of_arm N l r hl hlr hr A p
      hs.1 ht hs.2.1 hs.2.2 hb)

/-- Every original-graph leaf of the actual filled frontier belongs to the
original source interval OR the physical full top, with no outside-bottom or
side contacts silently counted as source contacts. -/
theorem intervalArmFilled_frontier_leaf_mem_source_or_top
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N)) (hA : A ∈ intervalArmEvent N l r)
    (u v : RectangleVertex (0,0) N N)
    (huv : (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A)).Adj u v)
    (hunique : ∀ w, (openGraph (rectangleGraph (0,0) N N)
      (intervalArmFilledLeftFrontier N l r A)).Adj u w → w=v) :
    u.val.2=(N : ℤ) ∨ u ∈ intervalArmBottomArc N l r := by
  obtain ⟨hleft,hright⟩ := intervalArmFilled_region_seed_labels N l r hl hlr hr A hA
  have hF := intervalArmFilledLeftFrontier_eq_squareRegionFrontier N l r A
  rw [hF] at huv hunique
  exact squareRegion_frontier_leaf_mem_source_or_top N l r _ hleft hright u v huv hunique

end
end PottsContinuity.Push
