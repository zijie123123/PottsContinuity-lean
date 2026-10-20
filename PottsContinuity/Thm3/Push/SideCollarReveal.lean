module

public import PottsContinuity.Thm3.Push.SideCollarEvents
public import PottsContinuity.Thm3.Push.IntervalArmRightRecord
public import PottsContinuity.Thm3.Push.EmbeddedFixedRecordAgreement

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 Exploration
noncomputable section

/-- Original queries obtained by running the right filled exploration in the
fixed collar extension and reading back only original source bonds. -/
def sideCollarLeftArmReveal (w h : ℕ) (l r : ℤ)
    (C : Configuration (rectangleGraph (0,0) w h)) :
    Configuration (rectangleGraph (0,0) w h) :=
  embeddedConfigurationRestriction _ _ (sideCollarEmbedding w h) (sideCollarEmbedding_map_le w h)
    (intervalArmFilledRightReveal (sideCollarSize w h) (l+2) (r+2) (sideCollarExtension w h C))

end
end PottsContinuity.Push
