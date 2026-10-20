module

public import PottsContinuity.Thm3.Prop4.EvenSquareRawSourceBound

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- The complete even-square field package on the source stretched-decay
branch. The extra premise is kept explicit; this does not claim the stronger
unconditional package. -/
theorem evenSquarePairKernel_package_of_touch_and_stretchedDecay
    (q : Set.Ici (1 : ℝ)) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ)
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s)
    (hdecay : ∃ c₀ α : ℝ, 0 < c₀ ∧ 0 < α ∧ ∀ n : ℕ, 1 ≤ n →
      RSW.oneArmProbability μ n ≤ Real.exp (-c₀*(n : ℝ)^α)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
        RSW.maxSquarePairProbability (RSW.selfDualParameters q) (2*m) ≤
          A*prop4PairKernel c ε (RSW.oneArmProbability μ) m := by
  obtain ⟨c₀,α,hc₀,hα,hdecay⟩ := hdecay
  refine ⟨1,zero_lt_one,?_⟩
  intro ε hε hε1
  exact evenSquarePairKernel_of_touch q c₀ α ε hc₀ hα hε hε1 μ hμ hdecay hTouch

end
end PottsContinuity.Thm3.Prop4
