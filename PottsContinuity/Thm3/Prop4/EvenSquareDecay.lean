module

public import PottsContinuity.Thm3.Prop4.EvenSquareSummation
public import PottsContinuity.Thm3.Prop4.SummationDecay
public import PottsContinuity.Thm3.Prop4.OneArmRatio

/-!
# The actual-law consumer requiring only Lemma 7's even-square bound

The odd-square remark, exterior-circuit estimate and all numerical steps are
proved dependencies. The even-square estimate of Lemma 7 is the hypothesis
`hpair`; in `dualityQ_corrected_of_touch` (`Thm3.Prop4.RawSourceDecay`) it is
supplied from the touching estimate by `evenSquarePairKernel_of_touch`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm3.Prop4

/-- Complete downstream decay upgrade, conditional only on the actual uniform
even-square estimate for sufficiently small ε. No odd-square or numerical
recursion premise is added. -/
theorem oneArm_exponential_of_evenSquarePairBound (q : Set.Ici (1 : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 0 μ)
    (α c₀ ε₀ : ℝ) (hα : 0 < α) (hc₀ : 0 < c₀) (hε₀ : 0 < ε₀)
    (hdecay : ∀ n : ℕ, 1 ≤ n →
      RSW.oneArmProbability μ n ≤ Real.exp (-c₀*(n : ℝ)^α))
    (hpair : ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ m : ℕ, 1 ≤ m →
        RSW.maxSquarePairProbability (RSW.selfDualParameters q) (2*m) ≤
          A*prop4PairKernel c ε (RSW.oneArmProbability μ) m) :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℕ, 1 ≤ n →
      RSW.oneArmProbability μ n ≤ Real.exp (-d*(n : ℝ)) := by
  obtain ⟨ε,β,hε,hεβ,hβα,hβ1,hεε₀⟩ := exists_recursion_exponents hα hε₀
  obtain ⟨A,c,hA,hc,hpairε⟩ := hpair ε hε hεε₀
  let θ := RSW.selfDualParameters q
  let C := 1152*A*(1+1/PD.RCInfinite.openEnergy θ)
  have hC : 0 < C := by
    dsimp [C]
    have hρ := PD.RCInfinite.openEnergy_pos θ
    positivity
  obtain ⟨D,hD,hratio⟩ := oneArm_probability_upper_ratio θ μ hμ
  have ha : ∀ n : ℕ, 0 ≤ RSW.oneArmProbability μ n := fun _ => ENNReal.toReal_nonneg
  have hlim := weighted_stretched_exponential_tendsto_zero
    (RSW.oneArmProbability μ) hα hβα hc₀ ha hdecay
  have hsum := reweighted_summation_of_evenSquarePairBound θ μ hμ
    A c ε β hA hc hε hεβ hβ1 hlim.bddAbove_range hpairε
  exact exponential_bound_of_reweightedSummation (RSW.oneArmProbability μ) ha
    α c₀ C c ε β D hα hc₀ hC hc hε hεβ hβα hβ1 hD hratio hdecay hsum

end PottsContinuity.Thm3.Prop4
