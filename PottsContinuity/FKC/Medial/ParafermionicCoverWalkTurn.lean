-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverWalkTurn.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverExploration
public import PottsContinuity.FKC.Medial.ParafermionicCoverTurn
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial SimpleGraph
open LatticePort
noncomputable section

def parafermionicCoverFinitePairingStepTurn (n : ℕ)
    (A : Configuration (ParafermionicAmbientGraph n))
    (u v : ParafermionicCoverFinitePort n × Bool) : ℤ :=
  if u.2 = false ∧ v.2 = false then
    parafermionicCoverMedialTurnExponent
      (parafermionicCoverConfigurationExtensionState n A) u.1.1
  else 0

def parafermionicCoverFinitePairingWalkTurn (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u v) : ℤ :=
  (p.darts.map fun d => parafermionicCoverFinitePairingStepTurn n A d.fst d.snd).sum

theorem parafermionicCoverFinitePairingWalkTurn_append (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v w : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u v)
    (q : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk v w) :
    parafermionicCoverFinitePairingWalkTurn n hn A (p.append q) =
      parafermionicCoverFinitePairingWalkTurn n hn A p +
        parafermionicCoverFinitePairingWalkTurn n hn A q := by
  simp [parafermionicCoverFinitePairingWalkTurn, Walk.darts_append, List.map_append,
    List.sum_append]

end

end PottsContinuity.FKC.FiniteFK
