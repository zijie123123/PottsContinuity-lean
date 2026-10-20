module

public import PottsContinuity.Thm3.Prop4.EvenSquareRawSourceBound
public import PottsContinuity.Thm3.Prop4.EvenSquareDecay

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section

/-- The corrected upgrade of Proposition 4, from stretched-exponential to exponential decay
of the one-arm probability, with the corrected touching estimate of Lemma 6 kept as the
hypothesis `hTouch`. For Theorem 3 that hypothesis is supplied by
`Provider.touch_lower_bound` (through `Assembly.theorem_3_of_touch`), and for Theorem 2 in
`Thm4Plane.FinalRootRoutes`, in both cases from
`Thm3.Touch.selfDual_tilted_touch_all_slopes_corrected_of_reducedMarginal`. -/
theorem dualityQ_corrected_of_touch
    (q : Set.Ici (1 : ℝ)) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ)
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    (∃ c₀ α : ℝ, 0 < c₀ ∧ 0 < α ∧ ∀ n : ℕ, 1 ≤ n →
      RSW.oneArmProbability μ n ≤ Real.exp (-c₀*(n : ℝ)^α)) →
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      RSW.oneArmProbability μ n ≤ Real.exp (-c*(n : ℝ)) := by
  rintro ⟨c₀,α,hc₀,hα,hdecay⟩
  apply oneArm_exponential_of_evenSquarePairBound q μ hμ α c₀ 1 hα hc₀ zero_lt_one hdecay
  intro ε hε hε1
  exact evenSquarePairKernel_of_touch q c₀ α ε hc₀ hα hε hε1 μ hμ hdecay hTouch

end
end PottsContinuity.Thm3.Prop4
