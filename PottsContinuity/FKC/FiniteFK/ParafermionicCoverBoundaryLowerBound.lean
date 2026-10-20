-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverBoundaryLowerBound.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverSourcePhaseNormalization
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverLocalDefectCancellation
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
noncomputable section

local instance boundaryLowerBoundEdgeFintype (n : ℕ) :
    Fintype (ParafermionicAmbientGraph n).edgeSet := Fintype.ofFinite _
local instance boundaryLowerBoundEdgeDecidableEq (n : ℕ) :
    DecidableEq (ParafermionicAmbientGraph n).edgeSet := Classical.decEq _

/-- The source phase forces a uniformly positive actual free finite-FK
connection sum on the full exterior-neighbor boundary of the cover box. -/
theorem parafermionicCoverFiniteFreeBoundaryConnectionSum_lower
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n) :
    ‖parafermionicBoundaryCoefficient q‖ / 8 ≤
      ∑ v ∈ parafermionicCoverFiniteExteriorNeighborBoundary n,
        parafermionicCoverBoxOriginConnectionWeight n q v := by
  have hcoeff := parafermionicBoundaryCoefficient_norm_le_actual_defects q n hn
  have hzero : (∑ e : (ParafermionicAmbientGraph n).edgeSet,
      ‖parafermionicCoverContourFiniteEdgeDefect q n hn e‖) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    rw [parafermionicCoverContourFiniteEdgeDefect_eq_zero q n hn e]
    simp
  rw [hzero] at hcoeff
  linarith

/-- For each q in the strict source range, one positive constant works for
every finite cover-box size n≥1. -/
theorem parafermionicCoverFiniteFreeBoundaryConnectionSum_uniform_lower
    (q : ClusterWeight) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ ∑ v ∈ parafermionicCoverFiniteExteriorNeighborBoundary n,
        parafermionicCoverBoxOriginConnectionWeight n q v := by
  refine ⟨‖parafermionicBoundaryCoefficient q‖ / 8, ?_, ?_⟩
  · have hpos := parafermionicBoundaryCoefficient_norm_pos q
    positivity
  · intro n hn
    exact parafermionicCoverFiniteFreeBoundaryConnectionSum_lower q n hn

end
end PottsContinuity.FKC.FiniteFK
