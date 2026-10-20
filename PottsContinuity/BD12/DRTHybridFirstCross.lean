module

public import PottsContinuity.BD12.SelectedHybridFirstCross
public import PottsContinuity.BD12.DRTConditionalAssociation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! The first integrated hybrid cross bound for the actual finite weighted FK
law, with all q>=1, positive couplings, beta and boundary partitions. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory PD.FK
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance drtCrossEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance drtCrossEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- The unpinned positive-weight mean is exactly the actual DRT weighted mean. -/
theorem drt_pinnedMean_empty_eq (q : Set.Ioi (0 : ℝ)) (ξ : BoundaryCondition V)
    (J : G.edgeSet → Set.Ioi (0 : ℝ)) (β : Set.Ioi (0 : ℝ)) (g : Configuration G → ℝ) :
    finitePinnedMean (drtPositiveWeight G q ξ J β) ∅ ∅ g = drtMean G q ξ J β g := by
  rw [finitePinnedMean_eq_sum_law, finitePinnedLaw_empty]
  exact (drtMean_eq_sum_law G q ξ J β g).symm

end
end PottsContinuity.BD12
