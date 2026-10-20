-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RemainingConnectionRestoration.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.EdgeRestriction
public import PottsContinuity.FKC.FiniteFK.Wiring

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

/-- An actual connection in the graph of remaining edges reaches the target
after the genuinely open frozen edges are restored. The bridge from the
interface to the target is an actual connection in the same full graph. -/
theorem actualConnected_remaining_restoration_hits_target
    {V : Type*} {G : SimpleGraph V} [DecidableEq G.edgeSet]
    (R K : Configuration G)
    (A : Configuration (edgeRestriction G R))
    (x : V) (B T : Set V)
    (hbridge : ∀ y ∈ B, ∃ z ∈ T,
      ActualConnected G K y z)
    (hremaining : ∃ y ∈ B,
      ActualConnected (edgeRestriction G R) A x y) :
    ∃ z ∈ T, ActualConnected G
      ((edgeRestrictionConfigurationEquiv G R A).val ∪ K) x z := by
  obtain ⟨y, hyB, hxy⟩ := hremaining
  obtain ⟨z, hzT, hyz⟩ := hbridge y hyB
  have hrestored : ActualConnected G
      ((edgeRestrictionConfigurationEquiv G R A).val ∪ K) x y := by
    apply actualConnected_mono Finset.subset_union_left
    exact (actualConnected_edgeRestriction G R A x y).mp hxy
  exact ⟨z, hzT,
    hrestored.trans (actualConnected_mono Finset.subset_union_right hyz)⟩

end PottsContinuity.FKC.FiniteFK

