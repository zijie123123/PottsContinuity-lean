module

public import PottsContinuity.Thm3.Push.RectangleTopFrontier
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance frontierSelectorPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance frontierSelectorEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- A canonical separating frontier record: original revealed bonds together
with the entire actual open frontier. The selector makes no choice of a
non-unique simple crossing; the frontier is proved to contain a crossing. -/
abbrev TopFrontierRecord (a : LatticeVertex) (w h : ℕ) :=
  Configuration (rectangleGraph a w h) × Configuration (rectangleGraph a w h)

/-- Select the canonical top frontier on the actual crossing event, and none
otherwise. Both cases have their intended meaning on the whole carrier. -/
def rectangleTopFrontierSelector (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) : Option (TopFrontierRecord a w h) :=
  if A ∈ rectangleHorizontalCrossingEvent a w h then
    some (rectangleTopReveal a w h A, rectangleTopFrontier a w h A) else none

/-- A selected frontier witnesses actual crossing and all its bonds are open
in the original sample. -/
theorem rectangleTopFrontierSelector_spec (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (r : TopFrontierRecord a w h)
    (hr : rectangleTopFrontierSelector a w h A = some r) :
    r.2 ∈ rectangleHorizontalCrossingEvent a w h ∧ r.2 ⊆ A ∩ r.1 := by
  unfold rectangleTopFrontierSelector at hr
  split_ifs at hr with hA
  · have heq := Option.some.inj hr
    subst r
    exact ⟨rectangleTopFrontier_crosses a w h A hA,
      rectangleTopFrontier_subset_open_and_revealed a w h A⟩

/-- A top-frontier record is invariant under edits to every unrecorded
original bond. This concrete selector discharges the one-sided locality premise of
`extremalPathUpperRevealMap_stable`. -/
theorem rectangleTopFrontierSelector_oneSidedStable (a : LatticeVertex) (w h : ℕ)
    (A B : Configuration (rectangleGraph a w h)) (r : TopFrontierRecord a w h)
    (hr : rectangleTopFrontierSelector a w h A = some r)
    (hagree : B ∩ r.1 = A ∩ r.1) :
    rectangleTopFrontierSelector a w h B = some r := by
  unfold rectangleTopFrontierSelector at hr
  split_ifs at hr with hA
  · have heq := Option.some.inj hr
    subst r
    have hR := closedClusterReveal_stable (DualityExt.rectangleDualEdgeEquiv a w h)
      (rectangleDualTopPorts a w h) A B hagree
    have hF := rectangleTopFrontier_eq_of_reveal_agreement a w h A B hagree
    have hFB : rectangleTopFrontier a w h A ⊆ B := by
      intro f hf
      have hfa := rectangleTopFrontier_subset_open_and_revealed a w h A hf
      have hfb : f ∈ B ∩ rectangleTopReveal a w h A := by
        rw [hagree]
        exact hfa
      exact (Finset.mem_inter.mp hfb).1
    have hB : B ∈ rectangleHorizontalCrossingEvent a w h := by
      obtain ⟨u,v,hu,hv,hconn⟩ := rectangleTopFrontier_crosses a w h A hA
      exact ⟨u,v,hu,hv,actualConnected_mono hFB hconn⟩
    unfold rectangleTopFrontierSelector
    rw [ite_eq_left hB, hF]
    change some (closedClusterReveal _ _ B, _) = some (closedClusterReveal _ _ A, _)
    rw [hR]

end
end PottsContinuity.Push
