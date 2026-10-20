-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripOriginLowerBound.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeightMedian
public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeightSourceComparison
public import PottsContinuity.FKC.FiniteFK.StripCandidateCardinalityBound
public import PottsContinuity.FKC.FiniteFK.HorizontalStripOriginSmallestScale
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
noncomputable section

/-- The zero-tilt finite origin connection has the quantitative lower bound
from the canonical height median and the literal local-minimum candidate count.
The smallest rectangle uses its direct finite-energy estimate. -/
theorem horizontalStripOriginConnection_probability_lower_bound
    (q : PottsContinuity.FKC.ClusterWeight) {n m : ℕ}
    (hn : 1 ≤ n) (hnm : n ≤ m) :
    (1 / (5 * (n : ℝ)^2 * (m : ℝ)^2) : ℝ) ≤
      (measure (rectangleGraph (-(m : ℤ), 0) (2*m) n) q
        (BoundaryCondition.wired (horizontalStripOriginLocalWiredSet m n))
        (horizontalStripOriginLocalConnectionEvent m n)).toReal := by
  by_cases hm : 2 ≤ m
  · have hnpos : 0 < n := by omega
    obtain ⟨μ, hμ, _⟩ := horizontalStripTopWired_common_limit_height_sublevel_le_origin
      q n hnpos
    have hcanonical : μ = Classical.choose
        (horizontalStripTopWiredProbabilityMeasures_existsUnique_limit q n) := by
      let : NeBot (atTop : Filter ℕ) := atTop_neBot
      exact tendsto_nhds_unique hμ.1
        (Classical.choose_spec
          (horizontalStripTopWiredProbabilityMeasures_existsUnique_limit q n)).1
    have hheight := horizontalStripCanonicalHeight_probability_ge_half q n
    have hmedian :
        (1 / 2 : ℝ) ≤
          ((μ : Measure LatticeConfiguration)
            {ω | horizontalStripHeight n ω 0 ≤ n}).toReal := by
      simpa [hcanonical] using hheight
    have hsub := (hμ.2 m (by omega))
    let C : ℝ := (2 * (n*m) + 1) * (n+1)
    have hCpos : 0 < C := by positivity
    have hfrac : (1 / (2*C)) ≤
        ((μ : Measure LatticeConfiguration)
          {ω | horizontalStripHeight n ω 0 ≤ n}).toReal / C := by
      calc
        1 / (2*C) = (1 / 2 : ℝ) / C := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right hmedian (le_of_lt hCpos)
    have hrecip := stripCandidate_reciprocal_bound hn hnm hm
    have hrecipC :
        (1 / (5 * (n : ℝ)^2 * (m : ℝ)^2) : ℝ) ≤ 1 / (2*C) := by
      calc
        _ ≤ 1 / (2 * (2 * (n : ℝ) * (m : ℝ) + 1) * ((n : ℝ) + 1)) := hrecip
        _ = _ := by congr 1; ring
    change ((μ : Measure LatticeConfiguration)
        {ω | horizontalStripHeight n ω 0 ≤ n}).toReal / C ≤
      (measure (rectangleGraph (-(m : ℤ), 0) (2*m) n) q
        (BoundaryCondition.wired (horizontalStripOriginLocalWiredSet m n))
        (horizontalStripOriginLocalConnectionEvent m n)).toReal at hsub
    have hmain := le_trans hrecipC (le_trans hfrac hsub)
    simpa [C, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hmain
  · have hm1 : m = 1 := by omega
    have hn1 : n = 1 := by omega
    subst m
    subst n
    have hsmall := horizontalStripOriginLocalConnection_probability_gt_constants q
    norm_num at hsmall ⊢
    exact le_of_lt hsmall.2

end
end PottsContinuity.FKC.Medial
