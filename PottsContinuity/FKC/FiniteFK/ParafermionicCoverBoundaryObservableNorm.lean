-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverBoundaryObservableNorm.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverPathObservableSum
public import PottsContinuity.FKC.Medial.ParafermionicCoverContourSum
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverBoundarySums
public import Mathlib.Tactic
public import Mathlib.CategoryTheory.Countable
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial
noncomputable section

theorem parafermionicCoverExposedPhaseExpectation_norm_sum_le_boundary
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n) :
    (∑ c ∈ parafermionicCoverExposedCorners n,
      ‖parafermionicCoverPathPhaseExpectation q n hn (c.1, true)‖) ≤
      8 * (∑ v ∈ parafermionicCoverFiniteExteriorNeighborBoundary n,
        parafermionicCoverBoxOriginConnectionWeight n q v) := by
  calc
    (∑ c ∈ parafermionicCoverExposedCorners n,
      ‖parafermionicCoverPathPhaseExpectation q n hn (c.1, true)‖) ≤
        ∑ c ∈ parafermionicCoverExposedCorners n,
          parafermionicCoverBoxOriginConnectionWeight n q
            (parafermionicCoverExposedCornerVertex n c) := by
              apply Finset.sum_le_sum
              intro c hc
              have hconn := parafermionicCoverPathPhaseExpectation_norm_le_connection
                q n hn (c.1, true)
              have hv := parafermionicCoverExposedCorner_vertex_mem_box n c
              let μPath : @MeasureTheory.Measure
                  (Configuration (ParafermionicAmbientGraph n))
                  (pathObservableConfigMeasurableSpace n) :=
                @PMF.toMeasure _ (pathObservableConfigMeasurableSpace n)
                  (law (ParafermionicAmbientGraph n) q
                    (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))))
              let μBoundary : @MeasureTheory.Measure
                  (Configuration (ParafermionicAmbientGraph n))
                  (coverBoundarySumsConfigurationMeasurableSpace n) :=
                @PMF.toMeasure _ (coverBoundarySumsConfigurationMeasurableSpace n)
                  (law (ParafermionicAmbientGraph n) q
                    (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))))
              let E := {A | ActualConnected (ParafermionicAmbientGraph n) A
                (parafermionicCoverBoxOrigin n)
                (parafermionicCoverFinitePortPrimalVertex n c.1)}
              have hprob : (μPath E).toReal = (μBoundary E).toReal := by
                simp only [μPath, μBoundary]
              have hsub :
                  (⟨parafermionicCoverExposedCornerVertex n c, hv⟩ :
                    ParafermionicAmbientVertex n) =
                    parafermionicCoverFinitePortPrimalVertex n c.1 := by
                apply Subtype.ext
                rfl
              have hweight : parafermionicCoverBoxOriginConnectionWeight n q
                  (parafermionicCoverExposedCornerVertex n c) = (μBoundary E).toReal := by
                rw [parafermionicCoverBoxOriginConnectionWeight_subtype n q
                  ⟨parafermionicCoverExposedCornerVertex n c, hv⟩]
                rw [hsub]
              have hconn' :
                  ‖parafermionicCoverPathPhaseExpectation q n hn (c.1, true)‖ ≤
                    (μPath E).toReal := by
                simpa [μPath, E] using hconn
              exact hconn'.trans (le_of_eq (hprob.trans hweight.symm))
    _ ≤ 8 * (∑ v ∈ parafermionicCoverFiniteExteriorNeighborBoundary n,
        parafermionicCoverBoxOriginConnectionWeight n q v) :=
      parafermionicCoverExposedCorners_weighted_sum_le_eight_boundary n
        (parafermionicCoverBoxOriginConnectionWeight n q)
        (parafermionicCoverBoxOriginConnectionWeight_nonneg n q)

end
end PottsContinuity.FKC.FiniteFK
