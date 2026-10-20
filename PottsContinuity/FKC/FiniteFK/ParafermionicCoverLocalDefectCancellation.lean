-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverLocalDefectCancellation.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverTwoReturnProbability
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverZeroReturnDefect
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverDefectConfigurationSum
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial
noncomputable section

private theorem parafermionicCoverContourFiniteEdgeAtomicDefect_closed_probability_pair_cancel
    (n : ℕ) (hn : 1 ≤ n) (q : ClusterWeight)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A) :
    (configurationProbability (ParafermionicAmbientGraph n) q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A : ℂ) *
        parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A +
      (configurationProbability (ParafermionicAmbientGraph n) q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        (toggleEdgeConfiguration e A) : ℂ) *
        parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e
          (toggleEdgeConfiguration e A) = 0 := by
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  by_cases h0 : π 0 = 0
  · exact parafermionicCoverContourFiniteEdgeAtomicDefect_zero_return_probability_pair_eq_zero
      n hn q (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A e
      (by simpa [π] using h0)
  · by_cases h1 : π (π 0) = 0
    · exact parafermionicCoverContourFiniteEdgeAtomicDefect_two_return_free_probability_pair_cancel
        n hn q A e hclosed (by simpa [π] using h0) (by simpa [π] using h1)
    · exact parafermionicCoverContourFiniteEdgeAtomicDefect_three_return_probability_pair_cancel
        n hn q (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A e
        hclosed (by simpa [π] using h0) (by simpa [π] using h1)

/-- Under free finite FK probability, every actual configuration and its
edge-toggle make a zero weighted pair for the unchanged local atomic defect. -/
theorem parafermionicCoverContourFiniteEdgeAtomicDefect_probability_pair_cancel
    (n : ℕ) (hn : 1 ≤ n) (q : ClusterWeight)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (configurationProbability (ParafermionicAmbientGraph n) q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A : ℂ) *
        parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A +
      (configurationProbability (ParafermionicAmbientGraph n) q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        (toggleEdgeConfiguration e A) : ℂ) *
        parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e
          (toggleEdgeConfiguration e A) = 0 := by
  classical
  by_cases hclosed : e ∉ A
  · exact parafermionicCoverContourFiniteEdgeAtomicDefect_closed_probability_pair_cancel
      n hn q A e hclosed
  · have hopen : e ∈ A := by simpa using hclosed
    let B := toggleEdgeConfiguration e A
    have hBclosed : e ∉ B := by
      dsimp [B]
      rw [toggleEdgeConfiguration_mem]
      simp [hopen]
    have hpair := parafermionicCoverContourFiniteEdgeAtomicDefect_closed_probability_pair_cancel
      n hn q B e hBclosed
    simpa [B, toggleEdgeConfiguration_involutive, add_comm] using hpair

/-- The actual free-boundary expected finite edge defect vanishes, by averaging
the two genuine configurations in each edge-flip pair. -/
theorem parafermionicCoverContourFiniteEdgeDefect_eq_zero
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverContourFiniteEdgeDefect q n hn e = 0 := by
  rw [parafermionicCoverContourFiniteEdgeDefect_flip_pair_average]
  simp [parafermionicCoverContourFiniteEdgeAtomicDefect_probability_pair_cancel]

end
end PottsContinuity.FKC.FiniteFK
