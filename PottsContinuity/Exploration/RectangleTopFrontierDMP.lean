module

public import PottsContinuity.Thm3.Push.TopFrontierDMP
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Conditional law for the canonical upper rectangle frontier

This is the upper-side exploration of `Thm3.Push.TopFrontierDMP`, re-exported
through the Exploration namespace. Its selected value consists of the top closed-dual
reveal and the complete open primal frontier, which contains a horizontal
crossing. The value is not an individual highest crossing walk; this module
does not provide the general extremal-crossing exploration of Section 3 of the paper.
-/

@[expose] public section

namespace PottsContinuity.Exploration

open PottsContinuity.PD.FK

noncomputable section

local instance rectangleTopFrontierEdgeDecidableEq (a : LatticeVertex)
    (w h : ℕ) : DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _
local instance rectangleTopFrontierEdgeFintype (a : LatticeVertex)
    (w h : ℕ) : Fintype (rectangleGraph a w h).edgeSet := Fintype.ofFinite _
local instance rectangleTopFrontierRemainingFintype (a : LatticeVertex)
    (w h : ℕ) (R : Configuration (rectangleGraph a w h)) :
    Fintype (RemainingConfiguration (rectangleGraph a w h) R) := Fintype.ofFinite _

/-- The record type for the canonical top-port exploration of a finite
rectangle. The second component is its full open primal frontier. -/
abbrev rectangleTopFrontierRecord (a : LatticeVertex) (w h : ℕ) :=
  PottsContinuity.Push.TopFrontierRecord a w h

/-- Select the upper frontier record on the horizontal crossing event, and
`none` when no such crossing occurs. -/
def rectangleTopFrontierSelector (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    Option (rectangleTopFrontierRecord a w h) :=
  PottsContinuity.Push.rectangleTopFrontierSelector a w h A

/-- The reveal set of the canonical top-port frontier selector. -/
def rectangleTopFrontierReveal (a : LatticeVertex) (w h : ℕ) :=
  PottsContinuity.Push.rectangleTopFrontierReveal a w h

/-- The selected upper frontier record is stable under edits outside its
recorded top-side reveal. -/
theorem rectangleTopFrontierSelector_oneSidedStable
    (a : LatticeVertex) (w h : ℕ)
    (A B : Configuration (rectangleGraph a w h))
    (r : rectangleTopFrontierRecord a w h)
    (hr : rectangleTopFrontierSelector a w h A = some r)
    (hagree : B ∩ Prod.fst r = A ∩ Prod.fst r) :
    rectangleTopFrontierSelector a w h B = some r :=
  PottsContinuity.Push.rectangleTopFrontierSelector_oneSidedStable
    a w h A B r hr hagree

/-- The concrete top-frontier reveal is a stopping set. -/
theorem rectangleTopFrontierReveal_stable
    (a : LatticeVertex) (w h : ℕ)
    (A B : Configuration (rectangleGraph a w h))
    (hagree : B ∩ rectangleTopFrontierReveal a w h A =
      A ∩ rectangleTopFrontierReveal a w h A) :
    rectangleTopFrontierReveal a w h B = rectangleTopFrontierReveal a w h A :=
  PottsContinuity.Push.rectangleTopFrontierReveal_stable a w h A B hagree

end
end PottsContinuity.Exploration
