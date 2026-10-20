-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file
-- `FiniteFK/AdaptiveDomainMarkov.lean`.
-- Adaptation: renamed into PottsContinuity.Exploration and generalized
-- ClusterWeight to PD.FK.Parameters (independent 0 < p < 1 and 1 ≤ q).
module

public import PottsContinuity.PD.FK.ConditionalLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite stopping-set domain Markov property

The revealed edge set may depend on the configuration.  Its record includes
both the set and the open/closed states on that set.  Stability under agreement
on the recorded states makes each record fiber exactly a fixed-state fiber, so
the finite FK disintegration applies with the boundary partition induced by
the revealed open edges.
-/

@[expose] public section

namespace PottsContinuity.Exploration

open PottsContinuity.PD.FK

variable {V : Type*} [Finite V] {G : SimpleGraph V}

noncomputable section

local instance stoppingSetDMP_edgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance stoppingSetDMP_edgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance stoppingSetDMP_remainingFintype (R : Configuration G) :
    Fintype (RemainingConfiguration G R) := Fintype.ofFinite _

/-- The part of a configuration revealed by an exploration. -/
abbrev RevealMap := Configuration G → Configuration G

/-- The complete record fiber for one exploration: the revealed edge set and
the actual open/closed states recorded on it. -/
def revealRecordEvent (reveal : RevealMap (G := G)) (C₀ : Configuration G) :
    Set (Configuration G) :=
  {C | reveal C = reveal C₀ ∧ C ∩ reveal C₀ = C₀ ∩ reveal C₀}

/-- Store both the revealed set and its states as one finite statistic. -/
def revealRecordStatistic (reveal : RevealMap (G := G)) :
    Configuration G → Configuration G × Configuration G :=
  fun C => (reveal C, C ∩ reveal C)

/-- The recorded open edges, viewed as a state on the revealed edge set. -/
def revealRecordConfiguration (reveal : RevealMap (G := G)) (C₀ : Configuration G) :
    RemovedConfiguration G (reveal C₀) :=
  ⟨C₀ ∩ reveal C₀, Finset.inter_subset_right⟩

omit [Finite V] in
/-- If the exploration is stable under agreement on its recorded states, its
record fiber is precisely the event fixing those states. -/
theorem revealRecordEvent_eq_frozenStateEvent
    (reveal : RevealMap (G := G))
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (C₀ : Configuration G) :
    revealRecordEvent reveal C₀ =
      frozenStateEvent (reveal C₀) (revealRecordConfiguration reveal C₀) := by
  ext C
  constructor
  · intro h
    exact h.2
  · intro h
    have hstates : C ∩ reveal C₀ = C₀ ∩ reveal C₀ := by
      simpa [frozenStateEvent, revealRecordConfiguration] using h
    exact ⟨hstable C₀ C hstates, hstates⟩

/-- Conditioning a finite FK law on a stable exploration record leaves the
unrevealed-edge FK law.  The new boundary partition joins original boundary
identifications with connectivity through the recorded open edges; recorded
closed edges create no such connections. -/
theorem law_filter_revealRecord_map_remaining
    (q : Parameters) (ξ : BoundaryCondition V)
    (reveal : RevealMap (G := G))
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (C₀ : Configuration G) :
    ((law G q ξ).filter (revealRecordEvent reveal C₀)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent reveal hstable C₀]
        exact frozenStateEvent_support q ξ (reveal C₀)
          (revealRecordConfiguration reveal C₀))).map
        (fun C => (configurationSplitEquiv G (reveal C₀) C).1) =
      remainingLaw G q
        (frozenBoundary ξ (revealRecordConfiguration reveal C₀).val) (reveal C₀) := by
  have hevent := revealRecordEvent_eq_frozenStateEvent reveal hstable C₀
  simpa only [hevent] using law_filter_frozen_map_remaining q ξ
    (reveal C₀) (revealRecordConfiguration reveal C₀)

end
end PottsContinuity.Exploration
