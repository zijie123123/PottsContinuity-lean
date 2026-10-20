module

public import PottsContinuity.Thm4.FKCTurnBridge
public import PottsContinuity.Thm4.WindingBulk

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial MeasureTheory
noncomputable section

/-- The actual source suffix winding is 2*pi, proved from the geometric source
cycle; it is not assigned as a boundary value in the observable definition. -/
theorem pathWindingAtom_source (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverPathWindingAtom n hn A
      (parafermionicCoverFiniteOriginCornerPort n hn, true) = 2 * Real.pi := by
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  change (if hz : _ ∈ p.support then
    (Real.pi / 2) * (parafermionicCoverFinitePairingWalkTurn n hn A (p.dropUntil _ hz) : ℝ)
    else 0) = _
  rw [dite_eq_left p.start_mem_support, SimpleGraph.Walk.dropUntil_first,
    FKCBridge.exploration_turn_eq_four]
  push_cast
  ring

end
end PottsContinuity.Thm4
