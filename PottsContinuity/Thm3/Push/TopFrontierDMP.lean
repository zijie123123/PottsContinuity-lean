module

public import PottsContinuity.Thm3.Push.TopFrontierSelector
public import PottsContinuity.Exploration.ExtremalPathDMP
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.Exploration
noncomputable section
local instance topDMPOriginalEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _
local instance topDMPRemainingFintype (a : LatticeVertex) (w h : ℕ)
    (R : Configuration (rectangleGraph a w h)) :
    Fintype (RemainingConfiguration (rectangleGraph a w h) R) := Fintype.ofFinite _

/-- Reveal the canonical upper-frontier record, and the full configuration
when there is no crossing, as in the stopped-exploration convention of
`Exploration.ExtremalPathDMP`. -/
abbrev rectangleTopFrontierReveal (a : LatticeVertex) (w h : ℕ) :=
  extremalPathUpperRevealMap (rectangleTopFrontierSelector a w h) Prod.fst

theorem rectangleTopFrontierReveal_stable (a : LatticeVertex) (w h : ℕ)
    (A B : Configuration (rectangleGraph a w h))
    (hagree : B ∩ rectangleTopFrontierReveal a w h A =
      A ∩ rectangleTopFrontierReveal a w h A) :
    rectangleTopFrontierReveal a w h B = rectangleTopFrontierReveal a w h A :=
  extremalPathUpperRevealMap_stable _ _
    (rectangleTopFrontierSelector_oneSidedStable a w h) A B hagree

end
end PottsContinuity.Push
