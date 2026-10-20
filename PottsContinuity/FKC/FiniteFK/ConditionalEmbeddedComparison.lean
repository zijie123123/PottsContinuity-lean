-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ConditionalEmbeddedComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.Disintegration
public import PottsContinuity.FKC.FiniteFK.SubgraphComparison

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open FiniteProbability
open scoped BigOperators

noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
  (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
  (hGH : G.map f ≤ H)

local instance conditionalEmbeddedSmallEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance conditionalEmbeddedMappedEdgeFintype : Fintype (G.map f).edgeSet := Fintype.ofFinite _
local instance conditionalEmbeddedLargeEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance conditionalEmbeddedLargeEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _

private theorem eventIndicator_nonneg {α : Type*} (S : Set α) (x : α) :
    0 ≤ S.indicator (fun _ => (1 : ℝ)) x := by
  by_cases h : x ∈ S <;> simp [Set.indicator, h]

end

end PottsContinuity.FKC.FiniteFK
