-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripHeightSourceComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripCandidateProbability
public import PottsContinuity.FKC.FiniteFK.HorizontalStripSourceProbabilityBound
public import PottsContinuity.FKC.FiniteFK.HorizontalStripGoodEvent
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

open Filter Topology MeasureTheory

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
noncomputable section

private theorem probabilityMeasure_toReal_apply_eq_coe
    (μ : ProbabilityMeasure LatticeConfiguration) (s : Set LatticeConfiguration) :
    ((μ s : NNReal) : ℝ) = ((μ : Measure LatticeConfiguration) s).toReal := by
  let z : ENNReal := (μ : Measure LatticeConfiguration) s
  have htop : z ≠ (⊤ : ENNReal) := by
    exact measure_ne_top _ _
  have hcoe := ENNReal.coe_toNNReal htop
  change (z.toNNReal : ℝ) = z.toReal
  calc
    (z.toNNReal : ℝ) = (z.toNNReal : ENNReal).toReal := by simp
    _ = z.toReal := congrArg ENNReal.toReal hcoe

/-- The canonical top-wired strip limit bounds the height-sublevel probability
by the genuine finite wired probability, with the exact candidate count. -/
theorem horizontalStripTopWired_common_limit_height_sublevel_le_origin
    (q : PottsContinuity.FKC.ClusterWeight) (n : ℕ) (hn : 0 < n) :
    ∃! μ : ProbabilityMeasure LatticeConfiguration,
      Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ) ∧
      ∀ m : ℕ, 0 < m →
        (((μ {ω | horizontalStripHeight n ω 0 ≤ n} : ENNReal).toReal) /
            ((2 * (n * m) + 1) * (n + 1))) ≤
          (measure (rectangleGraph (-(m : ℤ), 0) (2 * m) n) q
            (BoundaryCondition.wired (horizontalStripOriginLocalWiredSet m n))
            (horizontalStripOriginLocalConnectionEvent m n)).toReal := by
  obtain ⟨μ, hμ, hμunique⟩ :=
    horizontalStripTopWired_common_limit_sourceA_le_origin q n
  refine ⟨μ, ⟨hμ.1, ?_⟩, ?_⟩
  · intro m hm
    obtain ⟨x, hx⟩ := exists_horizontalStripGoodCandidate_measure_lower_bound
      n m hn hm (μ : Measure LatticeConfiguration)
    let k := x.1.1
    let h := x.1.2
    have hh : h ≤ n := x.2.2
    have hset : horizontalStripGoodEvent n m k h hh =
        horizontalStripSourceAEvent n m k h hh := by
      ext ω
      exact (horizontalStripGoodEvent_iff_sourceAEvent n m k h hh ω)
    have hbound := hμ.2 m k h hh
    have hconvertGood := probabilityMeasure_toReal_apply_eq_coe μ
      (horizontalStripGoodEvent n m k h hh)
    rw [← hset] at hbound
    have hprob :
        ((μ (horizontalStripGoodEvent n m k h hh) : NNReal) : ℝ) ≤
          (measure (rectangleGraph (-(m : ℤ), 0) (2 * m) n) q
            (BoundaryCondition.wired (horizontalStripOriginLocalWiredSet m n))
            (horizontalStripOriginLocalConnectionEvent m n)).toReal := by
      exact hbound
    have hx' :
        ((μ : Measure LatticeConfiguration)
          {ω | horizontalStripHeight n ω 0 ≤ n}).toReal /
          ((2 * (n * m) + 1) * (n + 1)) ≤
        ((μ (horizontalStripGoodEvent n m k h hh) : NNReal) : ℝ) := by
      rw [hconvertGood]
      simpa [k, h] using hx
    exact le_trans hx' hprob
  · intro ν hν
    exact tendsto_nhds_unique hν.1 hμ.1

end
end PottsContinuity.FKC.Medial
