module

public import PottsContinuity.PD.FK.IsolatedBoundaryLaw
public import PottsContinuity.PD.FK.IncreasingEvents
public import PottsContinuity.PD.FK.RemainingComparison
public import PottsContinuity.PD.FK.Disintegration
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Restoring a source reveal after sampling an auxiliary configuration

Only the unrevealed auxiliary edge states are copied. Every recorded source
state is restored literally. The target law is the normalized source fiber,
not a probability conditioned on an additional connection event.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance replayOriginalEdgeEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Replace all states on the reveal by the fixed actual recorded state,
retaining the auxiliary states on every other original edge. -/
def replayRevealedState (R : Configuration G) (B : RemovedConfiguration G R)
    (C : Configuration G) : Configuration G := (C \ R) ∪ B.val

end
end PottsContinuity.Thm3.Prop4
