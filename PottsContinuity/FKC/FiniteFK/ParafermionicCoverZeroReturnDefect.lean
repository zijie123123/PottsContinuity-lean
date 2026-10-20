-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverZeroReturnDefect.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverDefectConfigurationSum
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutZeroVisitRouting
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

/-- When the actual terminal permutation returns immediately, the actual
edge-fiber atomic defect vanishes before and after toggling that edge. -/
theorem parafermionicCoverContourFiniteEdgeAtomicDefect_zero_return_pair_eq_zero
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 = 0) :
    parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A = 0 ∧
      parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e
        (toggleEdgeConfiguration e A) = 0 := by
  have hcard := (parafermionicCoverFiniteEdgeCutTerminalPermutation_zero_iff_edgeFalseVisits_zero
    n hn A e).mp hπ0
  have hno := (parafermionicCoverFiniteEdgeFalseVisits_card_eq_zero_iff
    n hn A e).mp hcard
  exact parafermionicCoverContourFiniteEdgeAtomicDefect_eq_zero_of_no_false_visit
    q n hn A e hno

/-- The zero-return atomic defect pair is also zero after weighting both
actual configurations by their finite FK probabilities. -/
theorem parafermionicCoverContourFiniteEdgeAtomicDefect_zero_return_probability_pair_eq_zero
    (n : ℕ) (hn : 1 ≤ n) (q : ClusterWeight)
    (ξ : BoundaryCondition (ParafermionicAmbientVertex n))
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 = 0) :
    (configurationProbability (ParafermionicAmbientGraph n) q ξ A : ℂ) *
        parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A +
      (configurationProbability (ParafermionicAmbientGraph n) q ξ
        (toggleEdgeConfiguration e A) : ℂ) *
        parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e
          (toggleEdgeConfiguration e A) = 0 := by
  obtain ⟨hA, hT⟩ :=
    parafermionicCoverContourFiniteEdgeAtomicDefect_zero_return_pair_eq_zero
      q n hn A e hπ0
  simp [hA, hT]

end
end PottsContinuity.FKC.FiniteFK
