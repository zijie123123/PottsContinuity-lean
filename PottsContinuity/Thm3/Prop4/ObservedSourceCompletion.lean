module

public import PottsContinuity.Thm3.Prop4.SourceRevealExtension

/-! # Source completion from observed sample data -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
variable {V : Type*} (G : SimpleGraph V)
local instance observedCompletionEdgeEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Two trace selectors observed by separate raw reveals are both observed
by any completion retaining their union. -/
theorem sourceTraces_observed_of_retained_union {T : Type*}
    (left right completed : Configuration G → Configuration G)
    (lower upper : Configuration G → T)
    (hleft : ∀ A C, C ∩ left A = A ∩ left A → left C = left A)
    (hright : ∀ A C, C ∩ right A = A ∩ right A → right C = right A)
    (hretain : ∀ A, left A ∪ right A ⊆ completed A)
    (hlower : ∀ A C, RSW.stoppingObservationMap left A =
      RSW.stoppingObservationMap left C → lower A = lower C)
    (hupper : ∀ A C, RSW.stoppingObservationMap right A =
      RSW.stoppingObservationMap right C → upper A = upper C)
    (A C : Configuration G)
    (hobs : RSW.stoppingObservationMap completed A =
      RSW.stoppingObservationMap completed C) : lower A = lower C ∧ upper A = upper C := by
  constructor
  · apply hlower A C
    exact raw_stoppingObservation_eq_of_retained_observation G left completed hleft
      (fun A => Finset.Subset.trans Finset.subset_union_left (hretain A)) A C hobs
  · apply hupper A C
    exact raw_stoppingObservation_eq_of_retained_observation G right completed hright
      (fun A => Finset.Subset.trans Finset.subset_union_right (hretain A)) A C hobs

end
end PottsContinuity.Thm3.Prop4
