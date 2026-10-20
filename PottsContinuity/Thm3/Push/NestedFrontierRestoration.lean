module

public import PottsContinuity.Thm3.Push.RectangleHeightCarrier
public import PottsContinuity.Thm3.Push.RectanglePathReplacement
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance nestedRestorePropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance nestedRestoreEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The actual filled frontier in a reference rectangle replaces crossing
segments even for a SHORTER target. Only its bottom ports need the lower
label: no unproved assertion that the random lower domain contains the
whole target rectangle is used. -/
theorem nested_crossing_after_filled_frontier_restoration
    (a : LatticeVertex) (w h H : ℕ) (hle : h ≤ H)
    (A₀ A B : Configuration (rectangleGraph a w H))
    (h₀ : A₀ ∈ rectangleHorizontalCrossingEvent a w H)
    (hfront : rectangleFilledTopFrontier a w H A₀ ⊆ A)
    (hout : B \ rectangleFilledTopReveal a w H A₀ ⊆ A)
    (hB : DualityExt.rectangleConfigurationRestriction
      (rectangle_height_subset a w h H hle) B ∈ rectangleHorizontalCrossingEvent a w h) :
    DualityExt.rectangleConfigurationRestriction
      (rectangle_height_subset a w h H hle) A ∈ rectangleHorizontalCrossingEvent a w h := by
  let hrect := rectangle_height_subset a w h H hle
  let hdual := rectangle_dual_height_subset a w h H hle
  let σ : RectangleDualVertex a w H → Bool :=
    fun z => decide (z ∉ rectangleBottomRegion a w H A₀)
  let ι := rectangleDualVertexEmbedding hdual
  apply rectangle_crossing_of_cut_restoration a w h (σ ∘ ι) ?_
    (DualityExt.rectangleConfigurationRestriction hrect A)
    (DualityExt.rectangleConfigurationRestriction hrect B) ?_ ?_ hB
  · intro z hz
    have hz' := rectangle_dual_height_bottom_port a w h H hle hz
    have hbot : ι z ∈ rectangleBottomRegion a w H A₀ :=
      mem_outsideSeedRegion_of_seed _ _ _ hz'
        (rectangleTopReached_avoids_bottom a w H A₀ h₀ hz')
    exact decide_eq_false (not_not_intro hbot)
  · rw [rectangle_labelCut_restriction hrect hdual σ]
    intro f hf
    rw [DualityExt.rectangleConfigurationRestriction,mem_embeddedConfigurationRestriction] at hf ⊢
    exact hfront hf
  · intro f hf hfb
    let g := embeddedEdgeEmbedding _ _ (DualityExt.rectangleVertexEmbedding hrect)
      (DualityExt.rectangleGraph_map_rectangleVertexEmbedding hrect) f
    have hgB : g ∈ B := by
      exact (mem_embeddedConfigurationRestriction _ _ _ _ B f).mp hfb
    have hnot : g ∉ rectangleFilledTopReveal a w H A₀ := by
      intro hgR
      have hfR : f ∈ auxiliaryRegionReveal (DualityExt.rectangleDualEdgeEquiv a w h)
          (ι ⁻¹' (rectangleBottomRegion a w H A₀)ᶜ) := by
        rw [rectangle_regionReveal_restriction hrect hdual]
        exact (mem_embeddedConfigurationRestriction _ _ _ _ _ f).mpr hgR
      obtain ⟨z,hz,hzR⟩ := (mem_auxiliaryRegionReveal _ _ f).mp hfR
      have hfalse : decide (ι z ∉ rectangleBottomRegion a w H A₀) = false := hf z hz
      exact (decide_eq_false_iff_not.mp hfalse) hzR
    exact (mem_embeddedConfigurationRestriction _ _ _ _ A f).mpr
      (hout (Finset.mem_sdiff.mpr ⟨hgB,hnot⟩))

/-- On an actual filled-exploration fiber all frontier bonds are already
open. Only the genuine retention of unexamined reference bonds is needed
to transfer the shorter actual crossing. -/
theorem nested_crossing_on_filled_record
    (a : LatticeVertex) (w h H : ℕ) (hle : h ≤ H)
    (A₀ A B : Configuration (rectangleGraph a w H))
    (h₀ : A₀ ∈ rectangleHorizontalCrossingEvent a w H)
    (hrecord : A ∩ rectangleFilledTopReveal a w H A₀ =
      A₀ ∩ rectangleFilledTopReveal a w H A₀)
    (hout : B \ rectangleFilledTopReveal a w H A₀ ⊆ A)
    (hB : DualityExt.rectangleConfigurationRestriction
      (rectangle_height_subset a w h H hle) B ∈ rectangleHorizontalCrossingEvent a w h) :
    DualityExt.rectangleConfigurationRestriction
      (rectangle_height_subset a w h H hle) A ∈ rectangleHorizontalCrossingEvent a w h := by
  apply nested_crossing_after_filled_frontier_restoration a w h H hle A₀ A B h₀ ?_ hout hB
  intro f hf
  have hfr := rectangleFilledTopFrontier_subset_open_and_revealed a w H A₀ hf
  have hfR := rectangleTopReveal_subset_filled a w H A₀ (Finset.mem_inter.mp hfr).2
  exact (Finset.mem_inter.mp (hrecord.symm ▸
    (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hfr).1,hfR⟩))).1

end
end PottsContinuity.Push
