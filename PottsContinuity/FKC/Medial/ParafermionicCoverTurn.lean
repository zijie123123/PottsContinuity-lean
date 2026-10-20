-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverTurn.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverPorts
public import PottsContinuity.FKC.Medial.MedialPortTurn

@[expose] public section

namespace PottsContinuity.FKC.Medial

open LatticePort

noncomputable section

def parafermionicCoverMedialTurnPositive (ω : ParafermionicCoverConfiguration)
    (c : ParafermionicCoverPort) : Bool :=
  medialTurnPositive (parafermionicCoverPortLocalBaseState ω c) c.1

def parafermionicCoverMedialTurnExponent (ω : ParafermionicCoverConfiguration)
    (c : ParafermionicCoverPort) : ℤ :=
  if parafermionicCoverMedialTurnPositive ω c then 1 else -1

end
end PottsContinuity.FKC.Medial
