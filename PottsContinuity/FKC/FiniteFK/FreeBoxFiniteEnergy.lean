-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/FreeBoxFiniteEnergy.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.FiniteEnergy
public import PottsContinuity.FKC.Frozen.FreeBoxLimitV1
public import PottsContinuity.FKC.FiniteFK.BoxExhaustion
public import PottsContinuity.FKC.FiniteFK.BoxLaw

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.FiniteFK.Internal

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance freeBoxFiniteEnergyEdgeDecidableEq (c : LatticeVertex) (r : ℕ) :
    DecidableEq (boxGraph c r).edgeSet := Classical.decEq _

variable {e : squareLattice.edgeSet}

private theorem boxProbabilityMeasure_apply_preimage (q : ClusterWeight)
    (c : LatticeVertex) (r : ℕ) (s : Set LatticeConfiguration)
    (hs : MeasurableSet s) :
    (boxProbabilityMeasure q c r : Measure LatticeConfiguration) s =
      measure (boxGraph c r) q (BoundaryCondition.free ∅)
        {A | boxConfiguration c r A ∈ s} := by
  change ((law (boxGraph c r) q (BoundaryCondition.free ∅)).map
    (boxConfiguration c r)).toMeasure s = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hs]
  rfl

end
end PottsContinuity.FKC.FiniteFK.Internal
