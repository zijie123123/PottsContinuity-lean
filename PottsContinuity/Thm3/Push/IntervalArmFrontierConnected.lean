module

public import PottsContinuity.Thm3.Push.IntervalArmComponentSource
public import PottsContinuity.Thm3.Push.IntervalArmLeafRootsUnique

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance armConnectedEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _

/-- All NONTRIVIAL filled-frontier vertices belong to one actual component.
Isolated original vertices are retained on the carrier and are not included
in this connectivity assertion. No wiring or component-connectivity premise
is supplied: every component's source leaf is proved to be the same vertex. -/
theorem intervalArmFilled_frontier_adj_vertices_connected
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N)) (hA : A ∈ intervalArmEvent N l r)
    (u v x y : RectangleVertex (0,0) N N)
    (huv : (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A)).Adj u v)
    (hxy : (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A)).Adj x y) :
    ActualConnected (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A) u x := by
  obtain ⟨s₁,t₁,hs₁,ht₁,hus,hut,hleaf₁,_⟩ :=
    intervalArmFilled_component_contains_source_and_top_leaves N l r hl hlr hr A hA u v huv
  obtain ⟨s₂,t₂,hs₂,ht₂,hxs,hxt,hleaf₂,_⟩ :=
    intervalArmFilled_component_contains_source_and_top_leaves N l r hl hlr hr A hA x y hxy
  obtain ⟨p₁⟩ := hus.symm.trans hut
  obtain ⟨p₂⟩ := hxs.symm.trans hxt
  have hroot := intervalArmFilled_source_leaf_roots_eq N l r hl hr A
    p₁ p₂ hs₁ ht₁ hs₂ ht₂ hleaf₁ hleaf₂
  subst s₂
  exact hus.trans hxs.symm

end
end PottsContinuity.Push
