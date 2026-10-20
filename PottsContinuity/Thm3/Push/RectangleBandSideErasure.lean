module

public import PottsContinuity.Thm3.Push.RectangleThreeSideBonds
public import PottsContinuity.Thm3.Push.EmbeddedArcErasure

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12
noncomputable section
local instance rectangleBandErasureEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _
local instance rectangleBandErasureProp (p : Prop) : Decidable p := Classical.propDecidable p
local instance rectangleBandErasureRemaining (a : LatticeVertex) (w h : ℕ)
    (R : Configuration (rectangleGraph a w h)) :
    Fintype (RemainingConfiguration (rectangleGraph a w h) R) := Fintype.ofFinite _

/-- The actual left-to-right connection in the original sampled bottom band.
Restriction retains every original open and closed bond; the finite source
carrier confines the entire path, including its endpoints. -/
def rectangleBandConnectionEvent (a : LatticeVertex) (w b h : ℕ) (hbh : b ≤ h) :
    Set (Configuration (rectangleGraph a w h)) :=
  {C | embeddedConfigurationRestriction (rectangleGraph a w b) (rectangleGraph a w h)
      (rectangleBandEmbedding a w b h hbh) (rectangleBandEmbedding_map_le a w b h hbh) C ∈
    arcsConnectionEvent (rectangleGraph a w b)
      {u | u.val.1 = a.1} {v | v.val.1 = a.1+(w:ℤ)}}

/-- Erasing exactly the three separate side-bond sets preserves the actual
band crossing whenever the band is strictly shorter than the whole box. -/
theorem rectangleBandConnectionEvent_sdiff_threeSideBonds
    (a : LatticeVertex) (w b h : ℕ) (hbh : b < h)
    (C : Configuration (rectangleGraph a w h)) :
    C \ rectangleThreeSideBonds a w h ∈ rectangleBandConnectionEvent a w b h hbh.le ↔
      C ∈ rectangleBandConnectionEvent a w b h hbh.le := by
  apply embedded_arcsConnection_sdiff_internal_edges
  intro u v huv he
  exact rectangleThreeSideBonds_band_internal a w b h hbh u v huv he

end
end PottsContinuity.Push
