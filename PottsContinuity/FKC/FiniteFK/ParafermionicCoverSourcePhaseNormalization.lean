-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverSourcePhaseNormalization.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverContourDefectEstimate
public import PottsContinuity.FKC.Medial.ParafermionicCoverSourceTurning
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial MeasureTheory
noncomputable section


local instance sourcePhaseNormEdgeFintype (n : ℕ) :
    Fintype (ParafermionicAmbientGraph n).edgeSet := Fintype.ofFinite _
local instance sourcePhaseNormEdgeDecidable (n : ℕ) :
    DecidableEq (ParafermionicAmbientGraph n).edgeSet := Classical.decEq _

/-- The actual source atom is the boundary phase, using the proved turn of
the original finite origin-exploration path. -/
theorem parafermionicCoverPathPhaseAtom_source_eq_boundaryPhase
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverPathPhaseAtom q n hn A
      (parafermionicCoverFiniteOriginCornerPort n hn, true) =
      parafermionicBoundaryPhase q := by
  rw [parafermionicCoverPathPhaseAtom_source,
    parafermionicCoverFiniteOriginExplorationPath_turn_eq_four n hn A]
  unfold parafermionicBoundaryPhase
  congr 1
  push_cast
  ring

/-- The source expectation under the genuine finite free FK law equals its
configuration-independent boundary phase. -/
theorem parafermionicCoverPathPhaseExpectation_source_eq_boundaryPhase
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n) :
    parafermionicCoverPathPhaseExpectation q n hn
      (parafermionicCoverFiniteOriginCornerPort n hn, true) =
      parafermionicBoundaryPhase q := by
  unfold parafermionicCoverPathPhaseExpectation
  have hpoint : (fun A => parafermionicCoverPathPhaseAtom q n hn A
      (parafermionicCoverFiniteOriginCornerPort n hn, true)) =
      fun _ => parafermionicBoundaryPhase q := by
    funext A
    exact parafermionicCoverPathPhaseAtom_source_eq_boundaryPhase q n hn A
  rw [hpoint, MeasureTheory.integral_const]
  simp [MeasureTheory.measureReal_def]

/-- The exact source coefficient is bounded by the existing actual-edge and
finite-boundary defect estimate. -/
theorem parafermionicBoundaryCoefficient_norm_le_actual_defects
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n) :
    ‖parafermionicBoundaryCoefficient q‖ ≤
      (∑ e : (ParafermionicAmbientGraph n).edgeSet,
        ‖parafermionicCoverContourFiniteEdgeDefect q n hn e‖) +
        8 * (∑ v ∈ parafermionicCoverFiniteExteriorNeighborBoundary n,
          parafermionicCoverBoxOriginConnectionWeight n q v) := by
  have hphase := parafermionicCoverPathPhaseExpectation_source_eq_boundaryPhase q n hn
  have hcoeff : parafermionicBoundaryCoefficient q =
      parafermionicCoverPathPhaseExpectation q n hn
        (parafermionicCoverFiniteOriginCornerPort n hn, true) - 1 := by
    unfold parafermionicBoundaryCoefficient
    rw [hphase]
  rw [hcoeff]
  change ‖parafermionicCoverPathPhaseExpectation q n hn
      (parafermionicCoverFiniteOriginCornerPort n hn, true) - 1‖ ≤
    (∑ e : (ParafermionicAmbientGraph n).edgeSet,
      ‖parafermionicCoverContourFiniteEdgeDefect q n hn e‖) +
      8 * (∑ v ∈ parafermionicCoverFiniteExteriorNeighborBoundary n,
        parafermionicCoverBoxOriginConnectionWeight n q v)
  exact parafermionicCoverPathPhaseExpectation_source_sub_one_norm_le_defects q n hn

end
end PottsContinuity.FKC.FiniteFK
