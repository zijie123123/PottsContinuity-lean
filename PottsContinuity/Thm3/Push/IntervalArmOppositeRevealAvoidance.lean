module

public import PottsContinuity.Thm3.Push.IntervalArmRightPathAvoidsLeftReveal
public import PottsContinuity.Thm3.Push.IntervalArmRightFrontierSource

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PlanarMixed
noncomputable section
local instance oppositeRevealEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _

/-- On the nonjoining branch, any actual left-frontier walk starting in the
first interval avoids every incident right-reveal bond. -/
theorem intervalArmLeft_path_avoids_right_reveal_incidence
    (N : ℕ) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₂ : 0 < l₂) (h₂ : l₂ ≤ r₂) (hr₂ : r₂ < (N : ℤ))
    (horder : r₁ < l₂)
    (A : Configuration (rectangleGraph (0,0) N N))
    (hA : A ∈ intervalArmPairEvent N l₁ r₁ l₂ r₂)
    (hno : A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A ∉
      BD12.arcsConnectionEvent (rectangleGraph (0,0) N N)
        (intervalArmBottomArc N l₁ r₁) (intervalArmBottomArc N l₂ r₂))
    {s t : RectangleVertex (0,0) N N}
    (p : (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l₁ r₁ A)).Walk s t)
    (hs : s ∈ intervalArmBottomArc N l₁ r₁) :
    ∀ u ∈ p.support, ∀ f : (rectangleGraph (0,0) N N).edgeSet,
      u ∈ f.val → f ∉ intervalArmFilledRightReveal N l₂ r₂ A := by
  have hL : intervalArmFilledLeftFrontier N l₁ r₁ A ⊆
      A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A :=
    ((intervalArmFilledLeftFrontier_subset_open_raw_record N l₁ r₁ A).trans
      (Finset.inter_subset_inter_left (intervalArmLeftReveal_subset_filled N l₁ r₁ A))).trans
      (Finset.inter_subset_inter_left Finset.subset_union_left)
  have hR : intervalArmFilledRightFrontier N l₂ r₂ A ⊆
      A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A :=
    (intervalArmFilledRightFrontier_subset_open_record N l₂ r₂ A).trans
      (Finset.inter_subset_inter_left Finset.subset_union_right)
  have havoid : ∀ u ∈ p.support, ¬ ∃ v,
      (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledRightFrontier N l₂ r₂ A)).Adj u v := by
    intro u hu huv
    obtain ⟨v,huv⟩ := huv
    obtain ⟨a,ha,hua⟩ := intervalArmFilledRight_frontier_adj_vertex_connects_source
      N l₂ r₂ hl₂ h₂ hr₂ A hA.2 u v huv
    exact hno ⟨s,hs,a,ha,(actualConnected_mono hL (p.takeUntil u hu).reachable).trans
      (actualConnected_mono hR hua)⟩
  have hstart : ∀ f : (rectangleGraph (0,0) N N).edgeSet,
      s ∈ f.val → f ∉ intervalArmFilledRightReveal N l₂ r₂ A := by
    intro f hsf hf
    exact havoid s p.start_mem_support
      (intervalArmFilledRight_bottom_before_reveal_has_frontier_adj N l₂ r₂ hl₂ h₂ hr₂ A hA.2
        s hs.1 (by have hsx:=hs.2.2; omega) f hf hsf)
  have hmixed : ∀ u ∈ p.support, ¬ (∃ f ∈ intervalArmFilledRightReveal N l₂ r₂ A,
      ∃ g : (rectangleGraph (0,0) N N).edgeSet,
        g ∉ intervalArmFilledRightReveal N l₂ r₂ A ∧ u ∈ f.val ∧ u ∈ g.val) := by
    intro u hu hmix
    obtain ⟨a,ha,hua⟩ := intervalArmFilledRight_attachment_connects_source
      N l₂ r₂ hl₂ h₂ hr₂ A hA.2 u hmix
    exact hno ⟨s,hs,a,ha,(actualConnected_mono hL (p.takeUntil u hu).reachable).trans
      (actualConnected_mono hR hua)⟩
  have h := unrevealed_incidence_propagates_along_walk (rectangleGraph (0,0) N N)
    (intervalArmFilledRightReveal N l₂ r₂ A) (openWalkUnderlying _ _ p)
    (by simpa only [openWalkUnderlying_support] using hmixed) hstart
  simpa only [openWalkUnderlying_support] using h

/-- All right attachments avoid every incident left-reveal bond on the
actual nonjoining source branch. -/
theorem intervalArmRight_attachment_avoids_left_reveal_incidence
    (N : ℕ) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₁ : 0 < l₁) (h₁ : l₁ ≤ r₁) (hr₁ : r₁ < (N : ℤ))
    (hl₂ : 0 < l₂) (h₂ : l₂ ≤ r₂) (hr₂ : r₂ < (N : ℤ))
    (horder : r₁ < l₂)
    (A : Configuration (rectangleGraph (0,0) N N))
    (hA : A ∈ intervalArmPairEvent N l₁ r₁ l₂ r₂)
    (hno : A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A ∉
      BD12.arcsConnectionEvent (rectangleGraph (0,0) N N)
        (intervalArmBottomArc N l₁ r₁) (intervalArmBottomArc N l₂ r₂))
    (u : RectangleVertex (0,0) N N)
    (hu : u ∈ intervalArmFilledRightAttachmentVertices N l₂ r₂ A)
    (f : (rectangleGraph (0,0) N N).edgeSet) (huf : u ∈ f.val) :
    f ∉ intervalArmFilledLeftReveal N l₁ r₁ A := by
  obtain ⟨s,hs,⟨p⟩⟩ := intervalArmFilledRight_attachment_connects_source N l₂ r₂ hl₂ h₂ hr₂ A hA.2 u hu
  exact intervalArmRight_path_avoids_left_reveal_incidence N l₁ r₁ l₂ r₂ hl₁ h₁ hr₁ horder A hA hno
    p.reverse hs u p.reverse.end_mem_support f huf

/-- All left attachments avoid every incident right-reveal bond, with the
same original source intervals and actual nonjoining event. -/
theorem intervalArmLeft_attachment_avoids_right_reveal_incidence
    (N : ℕ) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₁ : 0 < l₁) (h₁ : l₁ ≤ r₁) (hr₁ : r₁ < (N : ℤ))
    (hl₂ : 0 < l₂) (h₂ : l₂ ≤ r₂) (hr₂ : r₂ < (N : ℤ))
    (horder : r₁ < l₂)
    (A : Configuration (rectangleGraph (0,0) N N))
    (hA : A ∈ intervalArmPairEvent N l₁ r₁ l₂ r₂)
    (hno : A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A ∉
      BD12.arcsConnectionEvent (rectangleGraph (0,0) N N)
        (intervalArmBottomArc N l₁ r₁) (intervalArmBottomArc N l₂ r₂))
    (u : RectangleVertex (0,0) N N)
    (hu : u ∈ intervalArmFilledAttachmentVertices N l₁ r₁ A)
    (f : (rectangleGraph (0,0) N N).edgeSet) (huf : u ∈ f.val) :
    f ∉ intervalArmFilledRightReveal N l₂ r₂ A := by
  obtain ⟨s,hs,⟨p⟩⟩ := intervalArmFilled_attachment_connects_source N l₁ r₁ hl₁ h₁ hr₁ A hA.1 u hu
  exact intervalArmLeft_path_avoids_right_reveal_incidence N l₁ r₁ l₂ r₂ hl₂ h₂ hr₂ horder A hA hno
    p.reverse hs u p.reverse.end_mem_support f huf

end
end PottsContinuity.Push
