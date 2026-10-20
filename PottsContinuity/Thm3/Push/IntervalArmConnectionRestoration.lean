module

public import PottsContinuity.Thm3.Push.IntervalArmRemainingLowerBound
public import PottsContinuity.Thm3.Push.RemainingRestore
public import PottsContinuity.Thm3.Push.EmbeddedFrontierWiring

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.BD12
noncomputable section
local instance armConnectionRestoreEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _

/-- An actual active attachment connection, together with the actual original
record, joins the ORIGINAL source intervals. No virtual boundary edge is used. -/
theorem intervalArmJoint_active_connection_restores_sources
    (N : ℕ) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₁ : 0 < l₁) (h₁ : l₁ ≤ r₁) (hr₁ : r₁ < (N : ℤ))
    (hl₂ : 0 < l₂) (h₂ : l₂ ≤ r₂) (hr₂ : r₂ < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N))
    (hA : A ∈ intervalArmPairEvent N l₁ r₁ l₂ r₂)
    (B : Configuration (rectangleGraph (0,0) N N))
    (hrecord : B ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A =
      A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A)
    (hB : let G := rectangleGraph (0,0) N N
      let L := intervalArmFilledLeftReveal N l₁ r₁ A
      let R := intervalArmFilledRightReveal N l₂ r₂ A
      embeddedConfigurationRestriction (activeUnexaminedGraph G (L ∪ R)) G
        (Function.Embedding.subtype _) (activeUnexaminedGraph_map_le G (L ∪ R)) B ∈
        arcsConnectionEvent _ (twoRevealActiveLeftArc G L R) (twoRevealActiveRightArc G L R)) :
    B ∈ arcsConnectionEvent (rectangleGraph (0,0) N N)
      (intervalArmBottomArc N l₁ r₁) (intervalArmBottomArc N l₂ r₂) := by
  let G := rectangleGraph (0,0) N N
  let L := intervalArmFilledLeftReveal N l₁ r₁ A
  let R := intervalArmFilledRightReveal N l₂ r₂ A
  obtain ⟨u,hu,v,hv,huv⟩ := hB
  obtain ⟨s,hs,hus⟩ := intervalArmFilled_attachment_connects_source N l₁ r₁ hl₁ h₁ hr₁ A hA.1 u.val
    (twoRevealActiveLeftArc_mixed G L R u hu)
  obtain ⟨t,ht,hvt⟩ := intervalArmFilledRight_attachment_connects_source N l₂ r₂ hl₂ h₂ hr₂ A hA.2 v.val
    (twoRevealActiveRightArc_mixed G L R v hv)
  change B ∩ (L ∪ R)=A ∩ (L ∪ R) at hrecord
  have hK : A ∩ (L ∪ R) ⊆ B := by rw [← hrecord]; exact Finset.inter_subset_left
  have hL : intervalArmFilledLeftFrontier N l₁ r₁ A ⊆ B :=
    (((intervalArmFilledLeftFrontier_subset_open_raw_record N l₁ r₁ A).trans
      (Finset.inter_subset_inter_left (intervalArmLeftReveal_subset_filled N l₁ r₁ A))).trans
      (Finset.inter_subset_inter_left Finset.subset_union_left)).trans hK
  have hR : intervalArmFilledRightFrontier N l₂ r₂ A ⊆ B :=
    ((intervalArmFilledRightFrontier_subset_open_record N l₂ r₂ A).trans
      (Finset.inter_subset_inter_left Finset.subset_union_right)).trans hK
  have hmid : ActualConnected G B u.val v.val := actualConnected_mono
    (embeddedConfigurationEmbedding_restriction_subset _ _ (Function.Embedding.subtype _)
      (activeUnexaminedGraph_map_le G (L ∪ R)) B)
    (actualConnected_embeddedConfiguration _ _ (Function.Embedding.subtype _)
      (activeUnexaminedGraph_map_le G (L ∪ R)) _ huv)
  exact ⟨s,hs,t,ht,(actualConnected_mono hL hus).symm.trans
    (hmid.trans (actualConnected_mono hR hvt))⟩

/-- The same actual connection inclusion for a configuration of the full
remaining graph, after the original observed open bonds are restored. -/
theorem intervalArmJoint_remaining_connection_restores_sources
    (N : ℕ) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₁ : 0 < l₁) (h₁ : l₁ ≤ r₁) (hr₁ : r₁ < (N : ℤ))
    (hl₂ : 0 < l₂) (h₂ : l₂ ≤ r₂) (hr₂ : r₂ < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N))
    (hA : A ∈ intervalArmPairEvent N l₁ r₁ l₂ r₂)
    (C : Configuration (edgeRestriction (rectangleGraph (0,0) N N)
      (intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A)))
    (hC : let G := rectangleGraph (0,0) N N
      let L := intervalArmFilledLeftReveal N l₁ r₁ A
      let R := intervalArmFilledRightReveal N l₂ r₂ A
      embeddedConfigurationRestriction (activeUnexaminedGraph G (L ∪ R)) (edgeRestriction G (L ∪ R))
        (Function.Embedding.subtype _) (activeUnexaminedGraph_map_le_edgeRestriction G (L ∪ R)) C ∈
        arcsConnectionEvent _ (twoRevealActiveLeftArc G L R) (twoRevealActiveRightArc G L R)) :
    restoreRemainingConfiguration (rectangleGraph (0,0) N N) (intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A)
      ⟨A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A,Finset.inter_subset_right⟩ C ∈
      arcsConnectionEvent (rectangleGraph (0,0) N N)
        (intervalArmBottomArc N l₁ r₁) (intervalArmBottomArc N l₂ r₂) := by
  apply intervalArmJoint_active_connection_restores_sources N l₁ r₁ l₂ r₂
    hl₁ h₁ hr₁ hl₂ h₂ hr₂ A hA _ (restoreRemainingConfiguration_inter _ _ _ C)
  have hstates := active_restriction_restoreRemainingConfiguration (rectangleGraph (0,0) N N)
    (intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A)
    ⟨A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A,Finset.inter_subset_right⟩ C
  dsimp only
  exact hstates.symm ▸ hC

end
end PottsContinuity.Push
