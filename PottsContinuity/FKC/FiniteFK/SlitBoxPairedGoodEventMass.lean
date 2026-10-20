-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxPairedGoodEventMass.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverBoundaryLowerBound
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverBoundarySums
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverConnectionProbability
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverExtremalSheets
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverExtremalDecayLimit
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverSideBoundary
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverSideConnectionPositive
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverSideToSlitComparison
public import PottsContinuity.FKC.FiniteFK.SlitBoxBottomCenter
public import PottsContinuity.FKC.FiniteFK.SlitBoxHorizontalReflection
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC MeasureTheory

noncomputable section

/-- The source symmetric-pair event is exactly the paired good event used by
the actual reveal record, after reflecting the second hit back to the original
configuration. -/
theorem slitBoxPairedGoodEvent_eq_symmetricBottomPair
    (n : ℕ) (u : SlitBoxVertex n) :
    {A : Configuration (slitBoxGraph n) |
      A ∈ slitBoxWiredArcConnectionEvent n u ∧
        configurationIso (slitBoxGraphHorizontalReflectionIso n) A ∈
          slitBoxWiredArcConnectionEvent n u} =
      slitBoxWiredArcConnectionEvent n u ∩
        slitBoxWiredArcConnectionEvent n
          (slitBoxGraphHorizontalReflectionIso n u) := by
  let σ := slitBoxGraphHorizontalReflectionIso n
  let e := configurationIso σ
  have hσ : σ (σ u) = u := by
    apply Subtype.ext
    simp [σ, slitBoxGraphHorizontalReflectionIso,
      slitBoxHorizontalReflectionVertexEquiv_val]
  have hpre := slitBoxWiredArcConnectionEvent_horizontalReflection_preimage n (σ u)
  have hmem : ∀ A : Configuration (slitBoxGraph n),
      e A ∈ slitBoxWiredArcConnectionEvent n u ↔
        A ∈ slitBoxWiredArcConnectionEvent n (σ u) := by
    intro A
    have h := congrArg (fun S : Set (Configuration (slitBoxGraph n)) => A ∈ S) hpre
    simpa [e, σ, hσ, Set.mem_preimage] using h
  ext A
  simp only [Set.mem_ofPred_eq]
  exact and_congr_right fun _ => hmem A

end
end PottsContinuity.FKC.FiniteFK
