-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripLocalCutAlmostSure.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripLocalCutProbability
public import PottsContinuity.FKC.FiniteFK.HorizontalStripLocalCutClopen
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK

noncomputable section

theorem tendsto_horizontalStripLocalClosedCutFailure_probability_zero
    (q : PottsContinuity.FKC.ClusterWeight) (n : ℕ)
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ)) :
    Tendsto (fun M => ((μ : Measure LatticeConfiguration)
      (horizontalStripLocalClosedCutSuccess M n)ᶜ).toReal) atTop (𝓝 0) := by
  let κ : ℝ := 1 / (1 + PottsContinuity.FKC.loopWeight q)
  let ρ : ℝ := 1 - κ ^ (2 * n + 1)
  have hκpos : 0 < κ := by
    dsimp [κ]
    exact div_pos (by norm_num) (PottsContinuity.FKC.one_add_loopWeight_pos q)
  have hκnonneg : 0 ≤ κ := hκpos.le
  have hκle : κ ≤ 1 := by
    dsimp [κ]
    rw [div_le_one (PottsContinuity.FKC.one_add_loopWeight_pos q)]
    linarith [PottsContinuity.FKC.one_le_loopWeight q]
  have hκpow : κ ^ (2 * n + 1) ≤ 1 := pow_le_one₀ hκnonneg hκle
  have hρnonneg : 0 ≤ ρ := by dsimp [ρ]; linarith
  have hρlt : ρ < 1 := by
    have hpowpos : 0 < κ ^ (2 * n + 1) := pow_pos hκpos _
    dsimp [ρ]
    linarith
  have hpow : Tendsto (fun M : ℕ => ρ ^ M) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρnonneg hρlt
  have hupper : Tendsto
      (fun M : ℕ => 2 * ρ ^ M) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hpow
  have hle : ∀ᶠ M : ℕ in atTop,
      0 ≤ ((μ : Measure LatticeConfiguration)
        (horizontalStripLocalClosedCutSuccess M n)ᶜ).toReal :=
    Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  have hle' : ∀ᶠ M : ℕ in atTop,
      ((μ : Measure LatticeConfiguration)
        (horizontalStripLocalClosedCutSuccess M n)ᶜ).toReal ≤ 2 * ρ ^ M := by
    filter_upwards [Filter.Eventually.of_forall fun M =>
      horizontalStripLocalClosedCutFailure_probability_le_limit q n M μ hμ] with M hM
    simpa [ρ, κ] using hM
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper hle hle'

theorem horizontalStripLocalClosedCutSuccess_ae_exists
    (q : PottsContinuity.FKC.ClusterWeight) (n : ℕ)
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ)) :
    ∀ᵐ ω ∂(μ : Measure LatticeConfiguration),
      ∃ M : ℕ, ω ∈ horizontalStripLocalClosedCutSuccess M n := by
  let S : Set LatticeConfiguration := ⋃ M : ℕ,
    horizontalStripLocalClosedCutSuccess M n
  let badMeasure : ℝ :=
    ((μ : Measure LatticeConfiguration) Sᶜ).toReal
  have hbad_nonneg : 0 ≤ badMeasure := by
    exact ENNReal.toReal_nonneg
  have hbad_zero : badMeasure = 0 := by
    by_contra hne
    have hbad_pos : 0 < badMeasure := by
      by_contra hnot
      exact hne (le_antisymm (not_lt.mp hnot) hbad_nonneg)
    let ε : ℝ := badMeasure / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hevent : ∀ᶠ M : ℕ in atTop,
        ((μ : Measure LatticeConfiguration)
          (horizontalStripLocalClosedCutSuccess M n)ᶜ).toReal < ε := by
      have h := Metric.tendsto_nhds.1
        (tendsto_horizontalStripLocalClosedCutFailure_probability_zero q n μ hμ)
        ε hε
      filter_upwards [h] with M hM
      simpa [Real.dist_eq, abs_of_nonneg ENNReal.toReal_nonneg] using hM
    obtain ⟨M, hM⟩ := hevent.exists
    have hsubset : Sᶜ ⊆ (horizontalStripLocalClosedCutSuccess M n)ᶜ := by
      intro ω hω hsuccess
      apply hω
      exact Set.mem_iUnion.mpr ⟨M, hsuccess⟩
    have hmeas :
        ((μ : Measure LatticeConfiguration) Sᶜ) ≤
          (μ : Measure LatticeConfiguration)
            (horizontalStripLocalClosedCutSuccess M n)ᶜ :=
      measure_mono hsubset
    have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hmeas
    have : badMeasure < ε := by
      dsimp [badMeasure, ε]
      exact lt_of_le_of_lt hreal hM
    dsimp [ε] at this
    linarith
  have hbad_measure_zero : (μ : Measure LatticeConfiguration) Sᶜ = 0 := by
    have htop : ((μ : Measure LatticeConfiguration) Sᶜ) ≠ ⊤ :=
      measure_ne_top _ _
    have htoReal : (((μ : Measure LatticeConfiguration) Sᶜ).toReal) = 0 := hbad_zero
    have hzero_or_top := (ENNReal.toReal_eq_zero_iff _).mp htoReal
    rcases hzero_or_top with hz | ht
    · exact hz
    · exact (htop ht).elim
  have hae : ∀ᵐ ω ∂(μ : Measure LatticeConfiguration), ω ∉ Sᶜ :=
    (measure_eq_zero_iff_ae_notMem).1 hbad_measure_zero
  filter_upwards [hae] with ω hω
  have hω' : ω ∈ S := by simpa using hω
  exact Set.mem_iUnion.mp hω'

end
end PottsContinuity.FKC.Medial
