module

public import PottsContinuity.Thm3.Push.IntervalArmLeaves
public import PottsContinuity.Thm3.Push.IntervalArmTopContacts
public import PottsContinuity.Thm3.Push.IntervalArmSourceContacts
public import PottsContinuity.Thm3.Push.ForestComponentLeaves

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- EVERY nontrivial actual filled-frontier component has a source-interval
leaf and a full-top leaf, connected to its original root by actual frontier
bonds. This follows from forest leaves, exact source/top leaf localization,
and separate uniqueness of both kinds of boundary contact. -/
theorem intervalArmFilled_component_contains_source_and_top_leaves
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N)) (hA : A ∈ intervalArmEvent N l r)
    (u v : RectangleVertex (0,0) N N)
    (huv : (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A)).Adj u v) :
    ∃ s t : RectangleVertex (0,0) N N,
      s ∈ intervalArmBottomArc N l r ∧ t.val.2=(N : ℤ) ∧
      ActualConnected (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A) u s ∧
      ActualConnected (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A) u t ∧
      (∃! w, (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A)).Adj s w) ∧
      (∃! w, (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A)).Adj t w) := by
  obtain ⟨a,b,hab,hua,hub,hleafA,hleafB⟩ := forest_component_has_two_original_leaves _
    (intervalArmFilledLeftFrontier_isAcyclic N l r A) u v huv
  have hclass : ∀ c : RectangleVertex (0,0) N N,
      (∃! w, (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A)).Adj c w) →
      c.val.2=(N : ℤ) ∨ c ∈ intervalArmBottomArc N l r := by
    intro c hc
    obtain ⟨w,hw,hunique⟩ := hc
    exact intervalArmFilled_frontier_leaf_mem_source_or_top N l r hl hlr hr A hA c w hw hunique
  have habConn := hua.symm.trans hub
  rcases hclass a hleafA with ha | ha <;> rcases hclass b hleafB with hb | hb
  · exact (hab (intervalArmFilled_frontier_top_contacts_eq N l r A a b ha hb habConn)).elim
  · exact ⟨b,a,hb,ha,hub,hua,hleafB,hleafA⟩
  · exact ⟨a,b,ha,hb,hua,hub,hleafA,hleafB⟩
  · exact (hab (intervalArmFilled_frontier_source_contacts_eq N l r A a b ha hb habConn)).elim

end
end PottsContinuity.Push
