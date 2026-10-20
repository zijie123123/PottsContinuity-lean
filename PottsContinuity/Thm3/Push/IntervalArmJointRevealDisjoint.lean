module

public import PottsContinuity.Thm3.Push.IntervalArmOppositeRevealAvoidance
public import PottsContinuity.Thm3.Push.OppositeAttachmentDisjointness
public import PottsContinuity.Thm3.Push.RectangleGraphPreconnected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance jointDisjointEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _

/-- The two actual filled reveals have disjoint incident vertex sets on the
nonjoining branch. This is separation of ALL removed bonds, independently of
how their states are assigned in a reference comparison. -/
theorem intervalArmJoint_reveal_vertices_disjoint
    (N : ℕ) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₁ : 0 < l₁) (h₁ : l₁ ≤ r₁) (hr₁ : r₁ < (N : ℤ))
    (hl₂ : 0 < l₂) (h₂ : l₂ ≤ r₂) (hr₂ : r₂ < (N : ℤ))
    (horder : r₁ < l₂)
    (A : Configuration (rectangleGraph (0,0) N N))
    (hA : A ∈ intervalArmPairEvent N l₁ r₁ l₂ r₂)
    (hno : A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A ∉
      BD12.arcsConnectionEvent (rectangleGraph (0,0) N N)
        (intervalArmBottomArc N l₁ r₁) (intervalArmBottomArc N l₂ r₂)) :
    Disjoint {u | ∃ f ∈ intervalArmFilledLeftReveal N l₁ r₁ A, u ∈ f.val}
      {u | ∃ f ∈ intervalArmFilledRightReveal N l₂ r₂ A, u ∈ f.val} := by
  have hproper : ∃ g : (rectangleGraph (0,0) N N).edgeSet,
      g ∉ intervalArmFilledLeftReveal N l₁ r₁ A := by
    obtain ⟨s,hs,t,ht,⟨p⟩⟩ := intervalArmEvent_on_right_filled_frontier N l₂ r₂ hl₂ h₂ hr₂ A hA.2
    have hnil : ¬ p.Nil := by
      intro hn
      have heq := congrArg (fun z : RectangleVertex (0,0) N N => z.val.2) hn.eq
      have hs0 := hs.1
      have htN : t.val.2=(N : ℤ) := ht
      omega
    obtain ⟨f,hf,hpair⟩ := (openGraph_adj _ _ _ _).mp (p.adj_snd hnil)
    refine ⟨f,intervalArmRight_path_avoids_left_reveal_incidence
      N l₁ r₁ l₂ r₂ hl₁ h₁ hr₁ horder A hA hno p hs s p.start_mem_support f ?_⟩
    rw [hpair]
    exact Sym2.mem_mk_left _ _
  apply disjoint_reveal_vertices_of_opposite_attachment_avoidance (rectangleGraph (0,0) N N)
    (rectangle_graph_preconnected (0,0) N N) _ _ hproper
  · intro u hu f hf huf
    exact intervalArmLeft_attachment_avoids_right_reveal_incidence N l₁ r₁ l₂ r₂
      hl₁ h₁ hr₁ hl₂ h₂ hr₂ horder A hA hno u hu f huf hf
  · intro u hu f hf huf
    exact intervalArmRight_attachment_avoids_left_reveal_incidence N l₁ r₁ l₂ r₂
      hl₁ h₁ hr₁ hl₂ h₂ hr₂ horder A hA hno u hu f huf hf

end
end PottsContinuity.Push
