-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitScreenMonotonicity.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitScreenCrossingPruning
public import PottsContinuity.FKC.FiniteFK.SlitBoxConfigurationExtension

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

/-- Actual closed-dual screen reachability between fixed endpoint sets is a
lower set of the original finite slit-box configuration. -/
def slitScreenClosedDualReachabilityEvent (n : ℕ)
    (F : Finset LatticeVertex) (S T : Set LatticeVertex) :
    Set (Configuration (slitBoxGraph n)) :=
  {A | ∃ u ∈ S, ∃ v ∈ T,
    (slitScreenClosedDualInducedGraph (slitBoxConfigurationExtension n A) F).Reachable u v}

end
end PottsContinuity.FKC.FiniteFK

