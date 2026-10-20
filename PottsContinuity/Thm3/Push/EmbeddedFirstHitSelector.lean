module

public import PottsContinuity.Thm3.Push.SideCollarFirstHitFiber
public import PottsContinuity.Thm3.Push.EmbeddedReveal

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12
noncomputable section
local instance embeddedFirstHitEdgeEq {U : Type*} (H : SimpleGraph U) :
    DecidableEq H.edgeSet := Classical.decEq _

/-- Run the actual retained side-arm selector on the literal embedded
source states, with no query of unrelated host edges. -/
def embeddedSideFirstHitSelector {U : Type*} (w h : ℕ) (l r : ℤ)
    (H : SimpleGraph U) (f : RectangleVertex (0,0) w h ↪ U)
    (hGH : (rectangleGraph (0,0) w h).map f ≤ H) (C : Configuration H) :
    Option (SideCollarFirstHitRecord w h) :=
  sideCollarFirstHitSelector w h l r (embeddedConfigurationRestriction _ H f hGH C)

/-- The embedded selector succeeds exactly on the genuine restricted
rectangle side-arm event. All original states, including closed ones, enter. -/
theorem embeddedSideFirstHitSelector_isSome_iff {U : Type*} (w h : ℕ) (l r : ℤ)
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ (w:ℤ))
    (H : SimpleGraph U) (f : RectangleVertex (0,0) w h ↪ U)
    (hGH : (rectangleGraph (0,0) w h).map f ≤ H) (C : Configuration H) :
    (embeddedSideFirstHitSelector w h l r H f hGH C).isSome ↔
      embeddedConfigurationRestriction _ H f hGH C ∈ arcsConnectionEvent (rectangleGraph (0,0) w h)
        {a | a.val.2 = 0 ∧ l ≤ a.val.1 ∧ a.val.1 ≤ r} {b | b.val.1 = 0} :=
  sideCollarFirstHitSelector_isSome_iff w h l r hl hlr hr _

end
end PottsContinuity.Push
