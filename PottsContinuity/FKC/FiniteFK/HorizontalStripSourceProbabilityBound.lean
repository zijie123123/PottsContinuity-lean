-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripSourceProbabilityBound.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripSourceEventWeakLimit
public import PottsContinuity.FKC.FiniteFK.HorizontalStripSourceEventExtension
public import PottsContinuity.FKC.FiniteFK.HorizontalStripWindowTranslation
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Tactic

@[expose] public section

open Filter Topology MeasureTheory

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
noncomputable section

/-- Every fixed SourceA probability under the canonical top-wired strip limit
is bounded above by the genuine origin-based finite wired connection probability.
The common limit remains characterized by the actual canonical weak limit. -/
theorem horizontalStripTopWired_common_limit_sourceA_le_origin
    (q : PottsContinuity.FKC.ClusterWeight) (n : ℕ) :
    ∃! μ : ProbabilityMeasure LatticeConfiguration,
      Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ) ∧
      ∀ (m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n),
        ((μ (horizontalStripSourceAEvent n m k h hh) : NNReal) : ℝ) ≤
          (measure (rectangleGraph (-(m : ℤ), 0) (2 * m) n) q
            (BoundaryCondition.wired (horizontalStripOriginLocalWiredSet m n))
            (horizontalStripOriginLocalConnectionEvent m n)).toReal := by
  obtain ⟨μ, hμ, hμunique⟩ :=
    horizontalStripTopWired_common_limit_event_probabilities q n
  refine ⟨μ, ⟨hμ.1, ?_⟩, ?_⟩
  · intro m k h hh
    let R := horizontalStripBlockerCollarRadius m k
    let M : ℕ → ℕ := fun j => R + j
    have hM : Tendsto M atTop atTop := by
      apply tendsto_atTop_mono (f := fun j : ℕ => j) (g := M)
      · intro j
        simp [M]
      · exact tendsto_id
    have hweak : Tendsto (fun j => horizontalStripTopWiredProbabilityMeasures q n (M j))
        atTop (𝓝 μ) := hμ.1.comp hM
    have hreal := tendsto_horizontalStripSourceAEvent_toRealProbability_of_weak
      hweak n m k h hh
    let C : ℝ := (measure (rectangleGraph (-(m : ℤ), 0) (2 * m) n) q
      (BoundaryCondition.wired (horizontalStripOriginLocalWiredSet m n))
      (horizontalStripOriginLocalConnectionEvent m n)).toReal
    apply le_of_tendsto_of_tendsto' hreal tendsto_const_nhds
    intro j
    let N := M j
    have hN : horizontalStripBlockerCollarRadius m k ≤ N := by
      simp [N, M, R]
    let ξ := horizontalStripTopWiredBoundary N n
    have hξ : ξ.boundary ⊆ horizontalStripTopSidesSet N n := by
      intro v hv
      change v.val.2 = (2 * n : ℤ) at hv
      simp only [horizontalStripTopSidesSet, Set.mem_ofPred_eq]
      exact Or.inl hv
    have hmeasure := horizontalStripRectangleProbabilityMeasure_apply_sourceAEvent
      q N n m k h hh hN ξ
    have hfinite := horizontalStripWindow_finiteSource_probability_le_origin
      q N n m k h hh ξ hξ hN
    have hcoerce :
        ((horizontalStripTopWiredProbabilityMeasures q n N
          (horizontalStripSourceAEvent n m k h hh) : NNReal) : ℝ) =
          (measure (horizontalStripCutRectangle N n) q ξ
            (finiteRegionSourceEvent
              (horizontalStripWindowRegion N n m k h)
              (horizontalStripWindowWiredRegion N n m k h)
              (horizontalStripWindowRoot N n m k h hh hN))).toReal := by
      change (((horizontalStripRectangleProbabilityMeasure q N n ξ :
        Measure LatticeConfiguration)
          (horizontalStripSourceAEvent n m k h hh)).toNNReal : ℝ) = _
      rw [hmeasure]
      let z := measure (horizontalStripCutRectangle N n) q ξ
        (finiteRegionSourceEvent
          (horizontalStripWindowRegion N n m k h)
          (horizontalStripWindowWiredRegion N n m k h)
          (horizontalStripWindowRoot N n m k h hh hN))
      have hfiniteNeTop : z ≠ (⊤ : ENNReal) := by
        exact measure_ne_top _ _
      have hcoe := ENNReal.coe_toNNReal hfiniteNeTop
      change (z.toNNReal : ℝ) = z.toReal
      calc
        (z.toNNReal : ℝ) = (z.toNNReal : ENNReal).toReal := by simp
        _ = z.toReal := congrArg ENNReal.toReal hcoe
    change ((horizontalStripTopWiredProbabilityMeasures q n (M j)
      (horizontalStripSourceAEvent n m k h hh) : NNReal) : ℝ) ≤ C
    rw [show M j = N from rfl, hcoerce]
    exact hfinite
  · intro ν hν
    exact tendsto_nhds_unique hν.1 hμ.1

end
end PottsContinuity.FKC.Medial
