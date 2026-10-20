module

public import PottsContinuity.Thm3.Push.IntervalArmRightAttachments
public import PottsContinuity.Thm3.Push.PairedIntervalArmRecords
public import PottsContinuity.Thm3.Push.SquareRegionBottomIncidence
public import PottsContinuity.Thm3.Push.RevealWalkIncidence
public import PottsContinuity.PlanarMixed.CrosscutOpenWalks

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PlanarMixed
noncomputable section
local instance rightPathAvoidEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _

/-- A right source walk in the actual right frontier cannot touch any
nontrivial left-frontier vertex on the nonjoining branch. -/
theorem intervalArmRight_path_no_left_frontier_neighbor
    (N : ℕ) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₁ : 0 < l₁) (h₁ : l₁ ≤ r₁) (hr₁ : r₁ < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N))
    (hA : A ∈ intervalArmPairEvent N l₁ r₁ l₂ r₂)
    (hno : A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A ∉
      BD12.arcsConnectionEvent (rectangleGraph (0,0) N N)
        (intervalArmBottomArc N l₁ r₁) (intervalArmBottomArc N l₂ r₂))
    {s t : RectangleVertex (0,0) N N}
    (p : (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledRightFrontier N l₂ r₂ A)).Walk s t)
    (hs : s ∈ intervalArmBottomArc N l₂ r₂)
    (u : RectangleVertex (0,0) N N) (hu : u ∈ p.support) :
    ¬ ∃ v, (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l₁ r₁ A)).Adj u v := by
  rintro ⟨v,huv⟩
  obtain ⟨a,b,ha,hb,hua,hub,_,_⟩ := intervalArmFilled_component_contains_source_and_top_leaves
    N l₁ r₁ hl₁ h₁ hr₁ A hA.1 u v huv
  have hL : intervalArmFilledLeftFrontier N l₁ r₁ A ⊆
      A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A :=
    ((intervalArmFilledLeftFrontier_subset_open_raw_record N l₁ r₁ A).trans
      (Finset.inter_subset_inter_left (intervalArmLeftReveal_subset_filled N l₁ r₁ A))).trans
      (Finset.inter_subset_inter_left Finset.subset_union_left)
  have hR : intervalArmFilledRightFrontier N l₂ r₂ A ⊆
      A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A :=
    (intervalArmFilledRightFrontier_subset_open_record N l₂ r₂ A).trans
      (Finset.inter_subset_inter_left Finset.subset_union_right)
  exact hno ⟨a,ha,s,hs,(actualConnected_mono hL hua).symm.trans
    (actualConnected_mono hR (p.takeUntil u hu).reachable.symm)⟩

/-- A right source walk avoids EVERY bond of the filled left reveal incident
to its vertices. This is stronger than disjoint frontier traces and includes
the original boundary; the intervals must be strictly ordered. -/
theorem intervalArmRight_path_avoids_left_reveal_incidence
    (N : ℕ) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₁ : 0 < l₁) (h₁ : l₁ ≤ r₁) (hr₁ : r₁ < (N : ℤ))
    (horder : r₁ < l₂)
    (A : Configuration (rectangleGraph (0,0) N N))
    (hA : A ∈ intervalArmPairEvent N l₁ r₁ l₂ r₂)
    (hno : A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A ∉
      BD12.arcsConnectionEvent (rectangleGraph (0,0) N N)
        (intervalArmBottomArc N l₁ r₁) (intervalArmBottomArc N l₂ r₂))
    {s t : RectangleVertex (0,0) N N}
    (p : (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledRightFrontier N l₂ r₂ A)).Walk s t)
    (hs : s ∈ intervalArmBottomArc N l₂ r₂) :
    ∀ u ∈ p.support, ∀ f : (rectangleGraph (0,0) N N).edgeSet,
      u ∈ f.val → f ∉ intervalArmFilledLeftReveal N l₁ r₁ A := by
  have havoid := intervalArmRight_path_no_left_frontier_neighbor N l₁ r₁ l₂ r₂ hl₁ h₁ hr₁ A hA hno p hs
  have hstart : ∀ f : (rectangleGraph (0,0) N N).edgeSet,
      s ∈ f.val → f ∉ intervalArmFilledLeftReveal N l₁ r₁ A := by
    intro f hsf hf
    obtain ⟨hleft,hright⟩ := intervalArmFilled_region_seed_labels N l₁ r₁ hl₁ h₁ hr₁ A hA.1
    have hF := squareRegion_bottom_after_reveal_has_frontier_adj N l₁ r₁
      (intervalArmRightRegion N l₁ r₁ A)ᶜ hleft hright s hs.1 (by have hsl:=hs.2.1; omega)
      (by omega) f hf hsf
    rw [← intervalArmFilledLeftFrontier_eq_squareRegionFrontier] at hF
    exact havoid s p.start_mem_support hF
  have hmixed : ∀ u ∈ p.support, ¬ (∃ f ∈ intervalArmFilledLeftReveal N l₁ r₁ A,
      ∃ g : (rectangleGraph (0,0) N N).edgeSet,
        g ∉ intervalArmFilledLeftReveal N l₁ r₁ A ∧ u ∈ f.val ∧ u ∈ g.val) := by
    intro u hu hmix
    exact havoid u hu (intervalArmFilled_attachment_has_frontier_adj N l₁ r₁ hl₁ h₁ hr₁ A hA.1 u hmix)
  have h := unrevealed_incidence_propagates_along_walk (rectangleGraph (0,0) N N)
    (intervalArmFilledLeftReveal N l₁ r₁ A) (openWalkUnderlying _ _ p)
    (by simpa only [openWalkUnderlying_support] using hmixed) hstart
  simpa only [openWalkUnderlying_support] using h

end
end PottsContinuity.Push
