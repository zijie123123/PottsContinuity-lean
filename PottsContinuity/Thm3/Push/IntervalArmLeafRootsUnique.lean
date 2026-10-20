module

public import PottsContinuity.Thm3.Push.IntervalArmLeafRightPort

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- Source leaves of ANY two filled-frontier source-to-top arms have the SAME
root, even when their connected components have not yet been identified. Each
leaf supplies a right-region port; the other arm's root barrier orders it. -/
theorem intervalArmFilled_source_leaf_roots_eq
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N))
    {s₁ t₁ s₂ t₂ : RectangleVertex (0,0) N N}
    (p₁ : (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A)).Walk s₁ t₁)
    (p₂ : (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A)).Walk s₂ t₂)
    (hs₁ : s₁ ∈ intervalArmBottomArc N l r) (ht₁ : t₁.val.2=(N : ℤ))
    (hs₂ : s₂ ∈ intervalArmBottomArc N l r) (ht₂ : t₂.val.2=(N : ℤ))
    (hleaf₁ : ∃! w, (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A)).Adj s₁ w)
    (hleaf₂ : ∃! w, (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A)).Adj s₂ w) :
    s₁=s₂ := by
  obtain ⟨v₁,hv₁,hunique₁⟩ := hleaf₁
  obtain ⟨v₂,hv₂,hunique₂⟩ := hleaf₂
  obtain ⟨b₁,hcoord₁,hb₁⟩ := intervalArmFilled_source_leaf_has_right_port
    N l r hl hr A p₁ hs₁ ht₁ v₁ hv₁ hunique₁
  obtain ⟨b₂,hcoord₂,hb₂⟩ := intervalArmFilled_source_leaf_has_right_port
    N l r hl hr A p₂ hs₂ ht₂ v₂ hv₂ hunique₂
  rcases lt_trichotomy s₁.val.1 s₂.val.1 with hlt | heq | hgt
  · have hleft : b₁ ∈ intervalArmLeftDualPorts N s₂.val.1 := by
      apply (mem_intervalArmLeftDualPorts N s₂.val.1 b₁).mpr
      exact Or.inr ⟨by rw [hcoord₁],by rw [hcoord₁]; exact hlt⟩
    exact (intervalArmRightRegion_avoids_left_of_frontier_root N l r hl hr A p₂
      hs₂.1 ht₂ hs₂.2.1 hs₂.2.2 b₁ hleft hb₁).elim
  · exact Subtype.ext (Prod.ext heq (hs₁.1.trans hs₂.1.symm))
  · have hleft : b₂ ∈ intervalArmLeftDualPorts N s₁.val.1 := by
      apply (mem_intervalArmLeftDualPorts N s₁.val.1 b₂).mpr
      exact Or.inr ⟨by rw [hcoord₂],by rw [hcoord₂]; exact hgt⟩
    exact (intervalArmRightRegion_avoids_left_of_frontier_root N l r hl hr A p₁
      hs₁.1 ht₁ hs₁.2.1 hs₁.2.2 b₂ hleft hb₂).elim

end
end PottsContinuity.Push
