module

public import PottsContinuity.Exploration.FiniteStoppingSetDMP
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Finite ordered outermost selectors

For a finite family of candidates, recognizability of a candidate from an
exterior edge set is expressed by agreement of configurations on that edge set.
This module defines that agreement predicate, `candidateStatesAgree`. In the proof,
outermost circuits are selected by the envelope maximum of
`Exploration.FiniteEnvelopeMaxSelector`, applied to lattice polygon candidates in
`Thm3.OuterCircuit.SelectedRecord`; no laminar ordered family of circuits is used.
-/

@[expose] public section

namespace PottsContinuity.Exploration

open PottsContinuity.PD.FK

variable {V : Type*} [Finite V] {G : SimpleGraph V}
variable {I : Type*} [Fintype I] [LinearOrder I]

noncomputable section

local instance outerSelectorEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance outerSelectorEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance outerSelectorIndexDecidableEq : DecidableEq I := Classical.decEq _

omit [Finite V] in

/-- Equality of the open/closed states on a finite set of edges. -/
def candidateStatesAgree (C C' : Configuration G) (S : Finset G.edgeSet) : Prop :=
  ∀ e ∈ S, (e ∈ C ↔ e ∈ C')

omit [Finite V] in

end
end PottsContinuity.Exploration
