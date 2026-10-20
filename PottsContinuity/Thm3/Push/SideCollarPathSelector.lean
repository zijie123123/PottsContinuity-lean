module

public import PottsContinuity.Thm3.Push.SideCollarFrontier
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import PottsContinuity.PlanarTopology.SubpathExtraction
public import PottsContinuity.Thm3.Push.BoundaryPathCodeWitness
public import Mathlib.Data.Prod.Lex

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 Exploration
noncomputable section
local instance sideCollarPathVertexLinearOrder (w h : ℕ) :
    LinearOrder (RectangleVertex (0,0) w h) :=
  LinearOrder.lift' (fun v => toLex v.val) (fun _ _ he => Subtype.ext (toLex.injective he))

/-- Original queried bonds, original frontier and the complete endpoint and
chronological vertex code of its selected simple side arm. -/
abbrev SideCollarArmPathRecord (w h : ℕ) :=
  Configuration (rectangleGraph (0,0) w h) ×
    Configuration (rectangleGraph (0,0) w h) × List (RectangleVertex (0,0) w h)

/-- Select the least-coded path (`Exploration.boundaryClusterPathCodeSelector`) in the
concrete original side frontier.
Failure means that this frontier has no arm between the designated sides. -/
def sideCollarArmPathSelector (w h : ℕ) (l r : ℤ)
    (C : Configuration (rectangleGraph (0,0) w h)) : Option (SideCollarArmPathRecord w h) :=
  (boundaryClusterPathCodeSelector
    {a : RectangleVertex (0,0) w h | a.val.2 = 0 ∧ l ≤ a.val.1 ∧ a.val.1 ≤ r}
    {b | b.val.1 = 0} (sideCollarLeftArmFrontier w h l r C)).map
    (fun code => (sideCollarLeftArmReveal w h l r C,sideCollarLeftArmFrontier w h l r C,code))

/-- The selector succeeds exactly on the original confined side-arm event. -/
theorem sideCollarArmPathSelector_isSome_iff (w h : ℕ) (l r : ℤ)
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ (w:ℤ))
    (C : Configuration (rectangleGraph (0,0) w h)) :
    (sideCollarArmPathSelector w h l r C).isSome ↔
      C ∈ arcsConnectionEvent (rectangleGraph (0,0) w h)
        {a | a.val.2 = 0 ∧ l ≤ a.val.1 ∧ a.val.1 ≤ r} {b | b.val.1 = 0} := by
  simp only [sideCollarArmPathSelector,Option.isSome_map,boundaryClusterPathCodeSelector_isSome_iff]
  constructor
  · rintro ⟨a,ha,b,hb,⟨p⟩⟩
    exact ⟨a,ha,b,hb,actualConnected_mono
      (fun e he => (Finset.mem_inter.mp (sideCollarLeftArmFrontier_subset_open_record w h l r C he)).1)
      ⟨p.val⟩⟩
  · intro hC
    obtain ⟨a,ha,b,hb,hconn⟩ := sourceLeftArm_on_sideCollar_frontier w h l r hl hlr hr C hC
    obtain ⟨p,hp⟩ := hconn.exists_isPath
    exact ⟨a,ha,b,hb,⟨⟨p,hp⟩⟩⟩

/-- Every selected code decodes to an actual simple source-frontier path,
with its original bottom interval and full left side as endpoints. -/
theorem sideCollarArmPathSelector_spec (w h : ℕ) (l r : ℤ)
    (C : Configuration (rectangleGraph (0,0) w h)) (rec : SideCollarArmPathRecord w h)
    (hrec : sideCollarArmPathSelector w h l r C = some rec) :
    rec.1 = sideCollarLeftArmReveal w h l r C ∧
    rec.2.1 = sideCollarLeftArmFrontier w h l r C ∧
    ∃ a : RectangleVertex (0,0) w h, a.val.2 = 0 ∧ l ≤ a.val.1 ∧ a.val.1 ≤ r ∧
    ∃ b : RectangleVertex (0,0) w h, b.val.1 = 0 ∧
    ∃ p : (openGraph (rectangleGraph (0,0) w h) rec.2.1).Path a b,
      boundaryClusterPathCode rec.2.1 ⟨a,b,p⟩ = rec.2.2 := by
  obtain ⟨code,hcode,heq⟩ := Option.map_eq_some_iff.mp hrec
  cases heq
  obtain ⟨a,ha,b,hb,p,hp⟩ := boundaryPathCodeSelector_hasPath _ _ _ code hcode
  exact ⟨rfl,rfl,a,ha.1,ha.2.1,ha.2.2,b,hb,p,hp⟩

end
end PottsContinuity.Push
