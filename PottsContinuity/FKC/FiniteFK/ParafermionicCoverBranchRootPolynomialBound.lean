-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverBranchRootPolynomialBound.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripOriginLowerBound
public import PottsContinuity.FKC.FiniteFK.HorizontalStripAsymmetricOriginComparison
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverBranchRootComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial MeasureTheory
noncomputable section

attribute [local instance] configurationMeasurableSpace

/-- The branch root has a polynomial lower bound with an explicit conservative
constant. This combines the canonical height lower bound at width `n+1`, the
actual first-boundary restriction to the ordinary origin event at scale `n`,
and one true dual edge. -/
theorem measure_parafermionicCoverBranchRootEvent_ge_polynomial
    (n : ℕ) (hn : 1 ≤ n) (q : ClusterWeight) :
    (1 / (60 * (n : ℝ)^4) : ℝ) ≤
      (measure (rectangleDualBottomCollarInnerGraph n) q
        (BoundaryCondition.wired (rectangleDualBottomCollarInnerThreeSides n))
        (parafermionicCoverBranchRootEvent n hn)).toReal := by
  have houter := horizontalStripOriginConnection_probability_lower_bound q hn (Nat.le_succ n)
  have hcompare :=
    measure_horizontalStripOriginLocalConnection_le_ordinaryOriginEvent q n
  have hordinary :
      (1 / (5 * (n : ℝ)^2 * ((n+1 : ℕ) : ℝ)^2) : ℝ) ≤
      (measure (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n) q
        (BoundaryCondition.wired
          (generalRectangleDualBottomCoreAmbientBoundary (-(n:ℤ),0) (2*n) n))
        (parafermionicCoverEq24OrdinaryOriginEvent n)).toReal := by
    exact le_trans houter hcompare
  have hordinary' :
      (1 / (5 * (n : ℝ)^2 * ((n : ℝ) + 1)^2) : ℝ) ≤
      (measure (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n) q
        (BoundaryCondition.wired
          (generalRectangleDualBottomCoreAmbientBoundary (-(n:ℤ),0) (2*n) n))
        (parafermionicCoverEq24OrdinaryOriginEvent n)).toReal := by
    simpa only [Nat.cast_add, Nat.cast_one] using hordinary
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have hsquare : ((n : ℝ) + 1)^2 ≤ 4 * (n : ℝ)^2 := by nlinarith
  have hden :
      5 * (n : ℝ)^2 * ((n : ℝ) + 1)^2 ≤ 20 * (n : ℝ)^4 := by
    calc
      5 * (n : ℝ)^2 * ((n : ℝ) + 1)^2 ≤
          5 * (n : ℝ)^2 * (4 * (n : ℝ)^2) :=
        mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = 20 * (n : ℝ)^4 := by ring
  have hrecip :
      (1 / (20 * (n : ℝ)^4) : ℝ) ≤
        1 / (5 * (n : ℝ)^2 * ((n : ℝ) + 1)^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [hden]
  have hδ : (1 / 3 : ℝ) ≤ 1 / (1 + loopWeight q) := by
    apply (div_le_div_iff₀ (by norm_num) (one_add_loopWeight_pos q)).2
    nlinarith [loopWeight_lt_two q]
  have hδ_nonneg : 0 ≤ (1 / (1 + loopWeight q) : ℝ) :=
    div_nonneg (by norm_num) (one_add_loopWeight_pos q).le
  have hproduct :
      (1 / (60 * (n : ℝ)^4) : ℝ) ≤
        (1 / (1 + loopWeight q)) *
          (measure (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n) q
            (BoundaryCondition.wired
              (generalRectangleDualBottomCoreAmbientBoundary (-(n:ℤ),0) (2*n) n))
            (parafermionicCoverEq24OrdinaryOriginEvent n)).toReal := by
    calc
      (1 / (60 * (n : ℝ)^4) : ℝ) =
          (1 / 3 : ℝ) * (1 / (20 * (n : ℝ)^4)) := by
            field_simp [ne_of_gt hnpos]
            ring
      _ ≤ (1 / (1 + loopWeight q)) * (1 / (20 * (n : ℝ)^4)) :=
        mul_le_mul_of_nonneg_right hδ (by positivity)
      _ ≤ (1 / (1 + loopWeight q)) *
          (measure (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n) q
            (BoundaryCondition.wired
              (generalRectangleDualBottomCoreAmbientBoundary (-(n:ℤ),0) (2*n) n))
            (parafermionicCoverEq24OrdinaryOriginEvent n)).toReal :=
        mul_le_mul_of_nonneg_left (le_trans hrecip hordinary' ) hδ_nonneg
  exact le_trans hproduct (measure_parafermionicCoverBranchRootEvent_lower_bound n hn q)

/-- Every admissible strip layer inherits the same branch-root lower bound
under its actual conditional law. -/
theorem measure_parafermionicCoverBranchRootEvent_conditional_ge_polynomial
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (q : ClusterWeight)
    (K : RemovedConfiguration (ParafermionicAmbientGraph n)
      (subgraphRemovedEdges
        ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
        (ParafermionicAmbientGraph n))) :
    (1 / (60 * (n : ℝ)^4) : ℝ) ≤
    ((((law (ParafermionicAmbientGraph n) q
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).filter
      (frozenStateEvent
        (subgraphRemovedEdges
          ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
          (ParafermionicAmbientGraph n)) K)
      (frozenStateEvent_support q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        (subgraphRemovedEdges
          ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
          (ParafermionicAmbientGraph n)) K)).map
      (parafermionicCoverStripDualRestriction n k hk)).toMeasure
      (parafermionicCoverBranchRootEvent n hn)).toReal := by
  exact le_trans (measure_parafermionicCoverBranchRootEvent_ge_polynomial n hn q)
    (measure_parafermionicCoverBranchRootEvent_le_conditional n hn k hk q K)

end
end PottsContinuity.FKC.FiniteFK
