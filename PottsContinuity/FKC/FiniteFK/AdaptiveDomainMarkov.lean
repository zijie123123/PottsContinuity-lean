-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/AdaptiveDomainMarkov.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ConditionalLaw

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open FiniteProbability

noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance adaptiveDomainMarkovEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance adaptiveDomainMarkovEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- The record produced by a revealed edge set stores both which edges were
revealed and their open/closed states. -/
def revealRecordEvent (reveal : Configuration G → Configuration G)
    (C₀ : Configuration G) : Set (Configuration G) :=
  {C | reveal C = reveal C₀ ∧ C ∩ reveal C₀ = C₀ ∩ reveal C₀}

def revealRecordConfiguration (reveal : Configuration G → Configuration G)
    (C₀ : Configuration G) : RemovedConfiguration G (reveal C₀) :=
  ⟨C₀ ∩ reveal C₀, Finset.inter_subset_right⟩

omit [Finite V] in
/-- A stopping-set consistency condition makes the record event exactly the
actual event fixing the revealed set and its open/closed state. -/
theorem revealRecordEvent_eq_frozenStateEvent
    (reveal : Configuration G → Configuration G)
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (C₀ : Configuration G) :
    revealRecordEvent G reveal C₀ =
      frozenStateEvent (reveal C₀) (revealRecordConfiguration G reveal C₀) := by
  ext C
  constructor
  · intro h
    exact h.2
  · intro h
    have hrevealed := hstable C₀ C (by simpa [h])
    exact ⟨hrevealed, h⟩

/-- Under a consistent reveal map, filtering the genuine finite FK law on the
record and reading the remaining coordinates gives the FK law with precisely
the frozen boundary induced by that record. -/
theorem law_filter_revealRecord_map_remaining
    (q : ClusterWeight) (ξ : BoundaryCondition V)
    (reveal : Configuration G → Configuration G)
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (C₀ : Configuration G) :
    ((law G q ξ).filter (revealRecordEvent G reveal C₀)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent G reveal hstable C₀]
        exact frozenStateEvent_support q ξ (reveal C₀)
          (revealRecordConfiguration G reveal C₀))).map
        (fun C => (configurationSplitEquiv G (reveal C₀) C).1) =
    remainingLaw G q
        (frozenBoundary ξ (revealRecordConfiguration G reveal C₀).val) (reveal C₀) := by
  have hevent := revealRecordEvent_eq_frozenStateEvent G reveal hstable C₀
  simpa only [hevent] using law_filter_frozen_map_remaining q ξ (reveal C₀)
    (revealRecordConfiguration G reveal C₀)

end

end PottsContinuity.FKC.FiniteFK
