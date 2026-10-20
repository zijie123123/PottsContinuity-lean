-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedMedialStep.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverWalkCompass
public import PottsContinuity.FKC.Medial.ParafermionicCoverTurn
public import PottsContinuity.FKC.Medial.ParafermionicCoverPortCompass
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph

def parafermionicCoverCompassLinearTurnSum (ds : List (Fin 4)) : ℤ :=
  ((List.zip ds ds.tail).map fun ab => primalCompassQuarterTurn ab.1 ab.2).sum

end PottsContinuity.FKC.Medial
