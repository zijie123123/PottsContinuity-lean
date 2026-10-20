-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Frozen/FreeBoxLimitV1.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.BoxCompactness
public import PottsContinuity.FKC.Internal.FreeBoxLimit

@[expose] public section

open MeasureTheory Filter Topology
namespace PottsContinuity.FKC.FiniteFK

theorem freeBoxLimit_existsUnique (q : ClusterWeight) :
    ∃! μ : ProbabilityMeasure LatticeConfiguration,
      ∀ (c : ℕ → LatticeVertex) (r : ℕ → ℕ),
        (∀ n, latticeBox (c n) (r n) ⊆ latticeBox (c (n + 1)) (r (n + 1))) →
        (∀ v : LatticeVertex, ∃ n, v ∈ latticeBox (c n) (r n)) →
        Tendsto (fun n => boxProbabilityMeasure q (c n) (r n)) atTop (𝓝 μ) :=
by exact PottsContinuity.FKC.FiniteFK.Internal.freeBoxLimit_existsUnique

end PottsContinuity.FKC.FiniteFK
