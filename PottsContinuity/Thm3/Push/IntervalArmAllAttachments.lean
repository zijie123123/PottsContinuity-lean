module

public import PottsContinuity.Thm3.Push.SquareRegionAllMixedLocality
public import PottsContinuity.Thm3.Push.IntervalArmFrontierConnected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance armAttachmentEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _

/-- All original vertices incident to BOTH a revealed and an unrevealed
source-square bond. This includes the entire physical boundary and corners. -/
def intervalArmFilledAttachmentVertices (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) : Set (RectangleVertex (0,0) N N) :=
  {u | ∃ f ∈ intervalArmFilledLeftReveal N l r A,
    ∃ g : (rectangleGraph (0,0) N N).edgeSet,
      g ∉ intervalArmFilledLeftReveal N l r A ∧ u ∈ f.val ∧ u ∈ g.val}

/-- Every attachment is an actual filled-frontier vertex, with all previous
strict-interior hypotheses discharged by full cell-boundary parity. -/
theorem intervalArmFilled_attachment_has_frontier_adj
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N)) (hA : A ∈ intervalArmEvent N l r)
    (u : RectangleVertex (0,0) N N) (hu : u ∈ intervalArmFilledAttachmentVertices N l r A) :
    ∃ v, (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A)).Adj u v := by
  obtain ⟨f,hf,g,hg,huf,hug⟩ := hu
  obtain ⟨hleft,hright⟩ := intervalArmFilled_region_seed_labels N l r hl hlr hr A hA
  rw [intervalArmFilledLeftFrontier_eq_squareRegionFrontier]
  apply squareRegion_mixed_incidence_has_frontier_adj_all N (by omega) _ _ _ u f g hf hg huf hug
  · intro z hz
    exact hleft z ((mem_intervalArmLeftDualPorts N l z).mpr (Or.inl hz))
  · intro z hz
    exact hright z ((mem_intervalArmRightDualPorts N r z).mpr (Or.inl hz))

/-- ALL attachments, including boundary vertices, are connected by actual
OPEN frontier bonds; no geometric or virtual-wiring conclusion is assumed. -/
theorem intervalArmFilled_attachment_vertices_connected
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N)) (hA : A ∈ intervalArmEvent N l r)
    (u v : RectangleVertex (0,0) N N)
    (hu : u ∈ intervalArmFilledAttachmentVertices N l r A)
    (hv : v ∈ intervalArmFilledAttachmentVertices N l r A) :
    ActualConnected (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A) u v := by
  obtain ⟨u',huu⟩ := intervalArmFilled_attachment_has_frontier_adj N l r hl hlr hr A hA u hu
  obtain ⟨v',hvv⟩ := intervalArmFilled_attachment_has_frontier_adj N l r hl hlr hr A hA v hv
  exact intervalArmFilled_frontier_adj_vertices_connected N l r hl hlr hr A hA u u' v v' huu hvv

/-- Every attachment joins the ORIGINAL source interval by actual frontier
bonds. This applies to boundary attachments as well as interior ones. -/
theorem intervalArmFilled_attachment_connects_source
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N)) (hA : A ∈ intervalArmEvent N l r)
    (u : RectangleVertex (0,0) N N) (hu : u ∈ intervalArmFilledAttachmentVertices N l r A) :
    ∃ s ∈ intervalArmBottomArc N l r,
      ActualConnected (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A) u s := by
  obtain ⟨v,huv⟩ := intervalArmFilled_attachment_has_frontier_adj N l r hl hlr hr A hA u hu
  obtain ⟨s,t,hs,ht,hus,hut,_,_⟩ :=
    intervalArmFilled_component_contains_source_and_top_leaves N l r hl hlr hr A hA u v huv
  exact ⟨s,hs,hus⟩

end
end PottsContinuity.Push
