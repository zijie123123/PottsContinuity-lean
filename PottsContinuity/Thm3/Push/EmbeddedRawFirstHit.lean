module

public import PottsContinuity.Thm3.Push.SideCollarRawDetermination
public import PottsContinuity.Thm3.Push.EmbeddedFirstHitSelector

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section
local instance embeddedRawFirstHitEdgeEq {U : Type*} (H : SimpleGraph U) :
    DecidableEq H.edgeSet := Classical.decEq _

/-- The actual host bonds obtained from raw dual-cluster queries in the
restricted side rectangle. No auxiliary states belong to this record. -/
def embeddedSideRawFirstHitReveal {U : Type*} (w h : ℕ) (r : ℤ)
    (H : SimpleGraph U) (f : RectangleVertex (0,0) w h ↪ U)
    (hGH : (rectangleGraph (0,0) w h).map f ≤ H) (C : Configuration H) :
    Configuration H :=
  embeddedConfigurationEmbedding _ H f hGH
    (sideCollarRawLeftArmReveal w h r (embeddedConfigurationRestriction _ H f hGH C))

/-- Agreement on the raw host queries preserves the complete first-hit
selection, including failure, with no assumption on unread host states. -/
theorem embeddedSideFirstHitSelector_eq_of_raw_agreement {U : Type*}
    (w h : ℕ) (l r : ℤ) (H : SimpleGraph U)
    (f : RectangleVertex (0,0) w h ↪ U)
    (hGH : (rectangleGraph (0,0) w h).map f ≤ H)
    (C D : Configuration H)
    (hstates : D ∩ embeddedSideRawFirstHitReveal w h r H f hGH C =
      C ∩ embeddedSideRawFirstHitReveal w h r H f hGH C) :
    embeddedSideFirstHitSelector w h l r H f hGH D =
      embeddedSideFirstHitSelector w h l r H f hGH C := by
  apply sideCollarFirstHitSelector_eq_of_raw_agreement
  ext e
  have hmem := Finset.ext_iff.mp hstates (embeddedEdgeEmbedding _ H f hGH e)
  simpa only [Finset.mem_inter,embeddedSideRawFirstHitReveal,mem_embeddedConfigurationRestriction,
    embeddedConfigurationEmbedding_eq_map,Finset.mem_map'] using hmem

end
end PottsContinuity.Push
