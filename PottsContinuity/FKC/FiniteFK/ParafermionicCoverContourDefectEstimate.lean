-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverContourDefectEstimate.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverContourEdgeSum
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverBoundaryObservableNorm
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverPathObservable
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial
noncomputable section

local instance contourDefectEstimateEdgeFintype (n : ℕ) :
    Fintype (ParafermionicAmbientGraph n).edgeSet := Fintype.ofFinite _
local instance contourDefectEstimateEdgeDecidable (n : ℕ) :
    DecidableEq (ParafermionicAmbientGraph n).edgeSet := Classical.decEq _

/-- The source-to-target observable discrepancy is bounded by the sum of the
actual finite-edge defects and the actual finite-boundary connection weight. -/
theorem parafermionicCoverPathPhaseExpectation_source_sub_target_norm_le_defects
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n) :
    ‖parafermionicCoverPathPhaseExpectation q n hn
        (parafermionicCoverFiniteOriginCornerPort n hn, true) -
      parafermionicCoverPathPhaseExpectation q n hn
        (parafermionicCoverFiniteCornerPairPerm n
          (parafermionicCoverFiniteOriginCornerPort n hn), true)‖ ≤
      (∑ e : (ParafermionicAmbientGraph n).edgeSet,
        ‖parafermionicCoverContourFiniteEdgeDefect q n hn e‖) +
        8 * (∑ v ∈ parafermionicCoverFiniteExteriorNeighborBoundary n,
          parafermionicCoverBoxOriginConnectionWeight n q v) := by
  classical
  let source := parafermionicCoverPathPhaseExpectation q n hn
    (parafermionicCoverFiniteOriginCornerPort n hn, true)
  let target := parafermionicCoverPathPhaseExpectation q n hn
    (parafermionicCoverFiniteCornerPairPerm n
      (parafermionicCoverFiniteOriginCornerPort n hn), true)
  let defects := ∑ e : (ParafermionicAmbientGraph n).edgeSet,
    parafermionicCoverContourFiniteEdgeDefect q n hn e
  let boundary := ∑ e ∈ parafermionicCoverExposedCorners n,
    (if parafermionicCoverIncomingPrimalLeft e.1.1 then (1 : ℂ) else -1) *
      parafermionicCoverPathPhaseExpectation q n hn (e.1, true)
  have hcontour := parafermionicCoverPathPhaseExpectation_contour_edge_identity q n hn
  have hdiff : source - target = defects - boundary := by
    dsimp [source, target, defects, boundary]
    rw [hcontour]
    ring
  have hdefects : ‖defects‖ ≤
      ∑ e : (ParafermionicAmbientGraph n).edgeSet,
        ‖parafermionicCoverContourFiniteEdgeDefect q n hn e‖ := by
    dsimp [defects]
    exact norm_sum_le _ _
  have hboundary : ‖boundary‖ ≤
      8 * (∑ v ∈ parafermionicCoverFiniteExteriorNeighborBoundary n,
        parafermionicCoverBoxOriginConnectionWeight n q v) := by
    calc
      ‖boundary‖ ≤ ∑ e ∈ parafermionicCoverExposedCorners n,
          ‖(if parafermionicCoverIncomingPrimalLeft e.1.1 then (1 : ℂ) else -1) *
            parafermionicCoverPathPhaseExpectation q n hn (e.1, true)‖ := by
        dsimp [boundary]
        exact norm_sum_le _ _
      _ = ∑ e ∈ parafermionicCoverExposedCorners n,
          ‖parafermionicCoverPathPhaseExpectation q n hn (e.1, true)‖ := by
        apply Finset.sum_congr rfl
        intro e he
        have hsign :
            ‖(if parafermionicCoverIncomingPrimalLeft e.1.1 then
              (1 : ℂ) else -1)‖ = 1 := by
          cases parafermionicCoverIncomingPrimalLeft e.1.1 <;> norm_num
        rw [norm_mul]
        rw [hsign]
        simp
      _ ≤ 8 * (∑ v ∈ parafermionicCoverFiniteExteriorNeighborBoundary n,
          parafermionicCoverBoxOriginConnectionWeight n q v) :=
        parafermionicCoverExposedPhaseExpectation_norm_sum_le_boundary q n hn
  calc
    ‖source - target‖ = ‖defects - boundary‖ := by rw [hdiff]
    _ ≤ ‖defects‖ + ‖boundary‖ := norm_sub_le _ _
    _ ≤ (∑ e : (ParafermionicAmbientGraph n).edgeSet,
          ‖parafermionicCoverContourFiniteEdgeDefect q n hn e‖) +
          8 * (∑ v ∈ parafermionicCoverFiniteExteriorNeighborBoundary n,
            parafermionicCoverBoxOriginConnectionWeight n q v) :=
      add_le_add hdefects hboundary

/-- The target path-phase expectation is one, so the same estimate applies to
the deviation of the source expectation from one. -/
theorem parafermionicCoverPathPhaseExpectation_source_sub_one_norm_le_defects
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n) :
    ‖parafermionicCoverPathPhaseExpectation q n hn
        (parafermionicCoverFiniteOriginCornerPort n hn, true) - 1‖ ≤
      (∑ e : (ParafermionicAmbientGraph n).edgeSet,
        ‖parafermionicCoverContourFiniteEdgeDefect q n hn e‖) +
        8 * (∑ v ∈ parafermionicCoverFiniteExteriorNeighborBoundary n,
          parafermionicCoverBoxOriginConnectionWeight n q v) := by
  rw [← parafermionicCoverPathPhaseExpectation_target q n hn]
  exact parafermionicCoverPathPhaseExpectation_source_sub_target_norm_le_defects q n hn

end
end PottsContinuity.FKC.FiniteFK
