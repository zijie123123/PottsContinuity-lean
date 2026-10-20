module

public import PottsContinuity.Thm3.Push.IntervalArmRawRightDetermination
public import PottsContinuity.Thm3.Push.SideCollarFirstHitSelector

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section

/-- Restrict only the raw right dual-cluster queries to original bonds. -/
def sideCollarRawLeftArmReveal (w h : ℕ) (r : ℤ)
    (C : Configuration (rectangleGraph (0,0) w h)) :
    Configuration (rectangleGraph (0,0) w h) :=
  embeddedConfigurationRestriction _ _ (sideCollarEmbedding w h) (sideCollarEmbedding_map_le w h)
    (intervalArmRawRightReveal (sideCollarSize w h) (r+2) (sideCollarExtension w h C))

/-- Raw original queries suffice to recover their full auxiliary states. -/
theorem sideCollar_raw_auxiliary_agreement (w h : ℕ) (r : ℤ)
    (C D : Configuration (rectangleGraph (0,0) w h))
    (hCD : D ∩ sideCollarRawLeftArmReveal w h r C =
      C ∩ sideCollarRawLeftArmReveal w h r C) :
    sideCollarExtension w h D ∩
        intervalArmRawRightReveal (sideCollarSize w h) (r+2) (sideCollarExtension w h C) =
      sideCollarExtension w h C ∩
        intervalArmRawRightReveal (sideCollarSize w h) (r+2) (sideCollarExtension w h C) :=
  embedded_fixed_extension_record_agreement _ _ (sideCollarEmbedding w h)
    (sideCollarEmbedding_map_le w h) (sideCollarOpenEdges w h) _ C D hCD

/-- No filled-hole states are needed to determine the filled original query shape. -/
theorem sideCollarLeftArmReveal_eq_of_raw_agreement (w h : ℕ) (l r : ℤ)
    (C D : Configuration (rectangleGraph (0,0) w h))
    (hCD : D ∩ sideCollarRawLeftArmReveal w h r C =
      C ∩ sideCollarRawLeftArmReveal w h r C) :
    sideCollarLeftArmReveal w h l r D = sideCollarLeftArmReveal w h l r C := by
  unfold sideCollarLeftArmReveal
  rw [intervalArmFilledRightReveal_eq_of_raw_agreement _ _ _ _ _
    (by simpa only [Finset.ext_iff, Finset.mem_inter] using
      sideCollar_raw_auxiliary_agreement w h r C D hCD)]

/-- The selected primal frontier is determined by the raw original queries. -/
theorem sideCollarLeftArmFrontier_eq_of_raw_agreement (w h : ℕ) (l r : ℤ)
    (C D : Configuration (rectangleGraph (0,0) w h))
    (hCD : D ∩ sideCollarRawLeftArmReveal w h r C =
      C ∩ sideCollarRawLeftArmReveal w h r C) :
    sideCollarLeftArmFrontier w h l r D = sideCollarLeftArmFrontier w h l r C := by
  unfold sideCollarLeftArmFrontier
  rw [intervalArmFilledRightFrontier_eq_of_raw_agreement _ _ _ _ _
    (by simpa only [Finset.ext_iff, Finset.mem_inter] using
      sideCollar_raw_auxiliary_agreement w h r C D hCD)]

/-- Even the full path record is fixed by the smaller raw queries. -/
theorem sideCollarArmPathSelector_eq_of_raw_agreement (w h : ℕ) (l r : ℤ)
    (C D : Configuration (rectangleGraph (0,0) w h))
    (hCD : D ∩ sideCollarRawLeftArmReveal w h r C =
      C ∩ sideCollarRawLeftArmReveal w h r C) :
    sideCollarArmPathSelector w h l r D = sideCollarArmPathSelector w h l r C := by
  unfold sideCollarArmPathSelector
  rw [sideCollarLeftArmFrontier_eq_of_raw_agreement w h l r C D hCD,
    sideCollarLeftArmReveal_eq_of_raw_agreement w h l r C D hCD]

/-- Both successful and failed first-hit selections are read from raw queries. -/
theorem sideCollarFirstHitSelector_eq_of_raw_agreement (w h : ℕ) (l r : ℤ)
    (C D : Configuration (rectangleGraph (0,0) w h))
    (hCD : D ∩ sideCollarRawLeftArmReveal w h r C =
      C ∩ sideCollarRawLeftArmReveal w h r C) :
    sideCollarFirstHitSelector w h l r D = sideCollarFirstHitSelector w h l r C := by
  unfold sideCollarFirstHitSelector
  rw [sideCollarArmPathSelector_eq_of_raw_agreement w h l r C D hCD]

end
end PottsContinuity.Push
