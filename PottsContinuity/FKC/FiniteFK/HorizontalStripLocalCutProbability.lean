-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripLocalCutProbability.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripLocalCutClopen
public import PottsContinuity.FKC.FiniteFK.HorizontalStripLocalCutTransport
public import PottsContinuity.FKC.FiniteFK.HorizontalStripLocalCutFailure
public import PottsContinuity.FKC.FiniteFK.HorizontalStripTopExhaustion
public import PottsContinuity.FKC.FiniteFK.HorizontalStripRectangleLaw
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK

noncomputable section

private theorem horizontalStripLocalCutProbability_toReal_eq_coe
    (μ : ProbabilityMeasure LatticeConfiguration) (s : Set LatticeConfiguration) :
    ((μ s : NNReal) : ℝ) = ((μ : Measure LatticeConfiguration) s).toReal := by
  let z : ENNReal := (μ : Measure LatticeConfiguration) s
  have htop : z ≠ (⊤ : ENNReal) := measure_ne_top _ _
  have hcoe := ENNReal.coe_toNNReal htop
  change (z.toNNReal : ℝ) = z.toReal
  calc
    (z.toNNReal : ℝ) = (z.toNNReal : ENNReal).toReal := by simp
    _ = z.toReal := congrArg ENNReal.toReal hcoe

private theorem horizontalStripLocalCutFailure_preimage_set
    (N n M : ℕ) (hMN : M ≤ N) :
    {A : Configuration (horizontalStripCutRectangle N n) |
      horizontalStripRectanglePlaneExtension N n A ∈
        (horizontalStripLocalClosedCutSuccess M n)ᶜ} =
      horizontalStripLocalCutFailureEvent N n M := by
  ext A
  change ¬ (horizontalStripRectanglePlaneExtension N n A ∈
    horizontalStripLocalClosedCutSuccess M n) ↔
      A ∈ horizontalStripLocalCutFailureEvent N n M
  rw [horizontalStripLocalClosedCutSuccess_closedExtension_preimage_iff
    N n M hMN A]
  exact not_not

theorem horizontalStripLocalClosedCutFailure_probability_le_limit
    (q : ClusterWeight) (n M : ℕ)
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ)) :
    (((μ : Measure LatticeConfiguration)
      (horizontalStripLocalClosedCutSuccess M n)ᶜ).toReal) ≤
      2 * (1 - (1 / (1 + loopWeight q)) ^ (2 * n + 1)) ^ M := by
  let μN := horizontalStripTopWiredProbabilityMeasures q n
  let E : Set LatticeConfiguration := (horizontalStripLocalClosedCutSuccess M n)ᶜ
  have hclopen := isClopen_horizontalStripLocalClosedCutFailure M n
  have hmeasure := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ
    hclopen
  have hreal : Tendsto (fun N => ((μN N E : NNReal) : ℝ)) atTop
      (𝓝 ((μ E : NNReal) : ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp hmeasure
  let B : ℝ := 2 * (1 - (1 / (1 + loopWeight q)) ^ (2 * n + 1)) ^ M
  have hbound : ∀ᶠ N : ℕ in atTop,
      ((μN N E : NNReal) : ℝ) ≤ B := by
    filter_upwards [Filter.eventually_atTop.2 ⟨M, fun N hNM => hNM⟩] with N hNM
    have h := horizontalStripLocalCutFailure_probability_le q N n M hNM
      (horizontalStripTopWiredBoundary N n)
    have hrealN : ((μN N E : NNReal) : ℝ) =
        (measure (horizontalStripCutRectangle N n) q
          (horizontalStripTopWiredBoundary N n)
          (horizontalStripLocalCutFailureEvent N n M)).toReal := by
      dsimp [μN, E, horizontalStripTopWiredProbabilityMeasures]
      rw [horizontalStripLocalCutProbability_toReal_eq_coe]
      rw [horizontalStripRectangleProbabilityMeasure_apply_preimage]
      · rw [horizontalStripLocalCutFailure_preimage_set N n M hNM]
      · exact hclopen.2.measurableSet
    rw [hrealN]
    exact h
  have htarget : (((μ : Measure LatticeConfiguration) E).toReal) =
      ((μ E : NNReal) : ℝ) := by
    symm
    exact horizontalStripLocalCutProbability_toReal_eq_coe μ E
  rw [htarget]
  by_contra hnot
  have hgap : B < ((μ E : NNReal) : ℝ) := lt_of_not_ge hnot
  let ε : ℝ := (((μ E : NNReal) : ℝ) - B) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hevent : ∀ᶠ N : ℕ in atTop,
      dist (((μN N E : NNReal) : ℝ)) (((μ E : NNReal) : ℝ)) < ε :=
    (Metric.tendsto_nhds.1 hreal) ε hε
  have ⟨N, hN⟩ := (hbound.and hevent).exists
  have hlow : ((μ E : NNReal) : ℝ) - ε < ((μN N E : NNReal) : ℝ) := by
    have := abs_lt.mp hN.2
    linarith
  have : B < ((μN N E : NNReal) : ℝ) := by dsimp [ε] at hlow; linarith
  exact (not_lt_of_ge (hN.1)) this

end
end PottsContinuity.FKC.Medial
