module

public import PottsContinuity.Thm3.Push.SideCollarReveal
public import PottsContinuity.Thm3.Push.IntervalArmRightFrontier

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12
noncomputable section

/-- Original bonds of the auxiliary right frontier. All added collar edges
are removed by restriction to the source carrier. -/
def sideCollarLeftArmFrontier (w h : ℕ) (l r : ℤ)
    (C : Configuration (rectangleGraph (0,0) w h)) :
    Configuration (rectangleGraph (0,0) w h) :=
  embeddedConfigurationRestriction _ _ (sideCollarEmbedding w h) (sideCollarEmbedding_map_le w h)
    (intervalArmFilledRightFrontier (sideCollarSize w h) (l+2) (r+2) (sideCollarExtension w h C))

/-- Any subconfiguration of the deterministic extension is recovered after
its original bonds are restricted and the fixed collar is reattached. -/
theorem sideCollar_subconfiguration_recovered (w h : ℕ)
    (C : Configuration (rectangleGraph (0,0) w h))
    (A : Configuration (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h)))
    (hA : A ⊆ sideCollarExtension w h C) :
    A ⊆ sideCollarExtension w h
      (embeddedConfigurationRestriction _ _ (sideCollarEmbedding w h) (sideCollarEmbedding_map_le w h) A) := by
  classical
  intro e he
  rcases Finset.mem_union.mp (hA he) with hmap | hfixed
  · rw [embeddedConfigurationEmbedding_eq_map] at hmap
    obtain ⟨d,_,rfl⟩ := Finset.mem_map.mp hmap
    apply Finset.mem_union.mpr
    left
    rw [embeddedConfigurationEmbedding_eq_map]
    exact Finset.mem_map.mpr ⟨d,(mem_embeddedConfigurationRestriction _ _ _ _ _ d).mpr he,rfl⟩
  · exact Finset.mem_union.mpr (Or.inr hfixed)

/-- The source frontier consists of originally open queried bonds. -/
theorem sideCollarLeftArmFrontier_subset_open_record (w h : ℕ) (l r : ℤ)
    (C : Configuration (rectangleGraph (0,0) w h)) :
    sideCollarLeftArmFrontier w h l r C ⊆ C ∩ sideCollarLeftArmReveal w h l r C := by
  classical
  intro e he
  have haux := intervalArmFilledRightFrontier_subset_open_record _ _ _ (sideCollarExtension w h C)
    ((mem_embeddedConfigurationRestriction _ _ _ _ _ e).mp he)
  simp only [Finset.mem_inter] at haux
  apply Finset.mem_inter.mpr
  constructor
  · have hc := (mem_embeddedConfigurationRestriction _ _ _ _ _ e).mpr haux.1
    rwa [sideCollarExtension_restriction] at hc
  · exact (mem_embeddedConfigurationRestriction _ _ _ _ _ e).mpr haux.2

/-- Source success survives on the original frontier alone. -/
theorem sourceLeftArm_on_sideCollar_frontier (w h : ℕ) (l r : ℤ)
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ (w:ℤ))
    (C : Configuration (rectangleGraph (0,0) w h))
    (hC : C ∈ arcsConnectionEvent (rectangleGraph (0,0) w h)
      {a | a.val.2 = 0 ∧ l ≤ a.val.1 ∧ a.val.1 ≤ r} {b | b.val.1 = 0}) :
    sideCollarLeftArmFrontier w h l r C ∈ arcsConnectionEvent (rectangleGraph (0,0) w h)
      {a | a.val.2 = 0 ∧ l ≤ a.val.1 ∧ a.val.1 ≤ r} {b | b.val.1 = 0} := by
  obtain ⟨hl',hlr',hr'⟩ := sideCollar_interval_bounds w h l r hl hlr hr
  have haux := intervalArmEvent_on_right_filled_frontier _ _ _ hl' hlr' hr'
    (sideCollarExtension w h C) ((sideCollar_interval_top_iff_source_left w h l r hl hlr hr C).mpr hC)
  have hsub := sideCollar_subconfiguration_recovered w h C
    (intervalArmFilledRightFrontier (sideCollarSize w h) (l+2) (r+2) (sideCollarExtension w h C))
    (fun e he => by
      have hh := intervalArmFilledRightFrontier_subset_open_record
        (sideCollarSize w h) (l+2) (r+2) (sideCollarExtension w h C) he
      simp only [Finset.mem_inter] at hh
      exact hh.1)
  exact (sideCollar_interval_top_iff_source_left w h l r hl hlr hr _).mp
    (arcsConnectionEvent_isUpperSet _ _ hsub haux)

end
end PottsContinuity.Push
