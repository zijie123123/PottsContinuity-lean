-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/Percolation.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.Model
public import Mathlib.Probability.Distributions.Uniform

/-!
# The critical FK law at cluster weight one

At `q = 1`, every subset of the finite edge carrier has probability
`(1 / 2) ^ |E|`, and the law is the uniform PMF on all edge subsets.
The boundary partition has no effect on this law.
-/

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open scoped BigOperators

noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance percolationEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet

lemma configuration_card_le_edge_card (A : Configuration G) : A.card ≤ Nat.card G.edgeSet := by
  rw [Nat.card_eq_fintype_card]
  exact Finset.card_le_univ A

end

end PottsContinuity.FKC.FiniteFK
