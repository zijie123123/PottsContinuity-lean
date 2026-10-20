module

public import PottsContinuity.Thm3.Prop4.RawSourcePairKernel
public import PottsContinuity.Thm3.Prop4.CenteredSquareIso
public import PottsContinuity.Thm3.Prop4.SmallScale

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The actual uniform even-square maximum estimate, conditional only on
the touching estimate. -/
theorem evenSquarePairKernel_of_touch
    (q : Set.Ici (1 : ℝ)) (c₀ α ε : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α)
    (hε : 0 < ε) (hε1 : ε < 1) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ)
    (hdecay : ∀ m : ℕ, 1 ≤ m → RSW.oneArmProbability μ m ≤ Real.exp (-c₀*(m : ℝ)^α))
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      RSW.maxSquarePairProbability (RSW.selfDualParameters q) (2*m) ≤
        A*prop4PairKernel c ε (RSW.oneArmProbability μ) m := by
  obtain ⟨A,c,N,hA,hc,hN,hpair⟩ := source_pair_kernel_of_touch
    q c₀ α ε hc₀ hα hε hε1 μ hμ hdecay hTouch
  have heventual (m : ℕ) (hmN : N ≤ m) :
      RSW.maxSquarePairProbability (RSW.selfDualParameters q) (2*m) ≤
        A*prop4PairKernel c ε (RSW.oneArmProbability μ) m := by
    apply RSW.maxSquarePairProbability_le
    intro i j
    obtain ⟨u,v,hu,hv,hprob⟩ := squarePairProbability_even_centered (RSW.selfDualParameters q) m i j
    rw [hprob]
    exact hpair m hmN u v hu hv
  obtain ⟨C₀,hC₀,hfinite⟩ := finite_diagonal_penalty (RSW.oneArmProbability μ)
    (RSW.oneArmProbability_pos (RSW.selfDualParameters q) μ hμ) ε N
  let B := max A 1
  let C := max c C₀
  have hB : 0 < B := hA.trans_le (le_max_left _ _)
  have hC : 0 < C := hc.trans_le (le_max_left _ _)
  have ha : ∀ n, 0 ≤ RSW.oneArmProbability μ n := fun _ => ENNReal.toReal_nonneg
  refine ⟨B,C,hB,hC,?_⟩
  intro m hm
  by_cases hmN : N ≤ m
  · exact (heventual m hmN).trans (mul_le_mul (le_max_left _ _)
      (prop4PairKernel_mono_coefficient _ ha ε c C (le_max_left _ _) m)
      (prop4PairKernel_nonneg c ε _ hc.le ha m) hB.le)
  · calc
      _ ≤ 1 := maxSquarePairProbability_le_one (RSW.selfDualParameters q) _
      _ ≤ Real.exp (C₀*(m : ℝ)^ε)*(RSW.oneArmProbability μ m)^2 := hfinite m hm (by omega)
      _ ≤ prop4PairKernel C₀ ε (RSW.oneArmProbability μ) m :=
        diagonal_le_prop4PairKernel _ ha ε C₀ hC₀.le m
      _ ≤ prop4PairKernel C ε (RSW.oneArmProbability μ) m :=
        prop4PairKernel_mono_coefficient _ ha ε C₀ C (le_max_right _ _) m
      _ ≤ B*prop4PairKernel C ε (RSW.oneArmProbability μ) m :=
        le_mul_of_one_le_left (prop4PairKernel_nonneg C ε _ hC.le ha m) (le_max_right _ _)

end
end PottsContinuity.Thm3.Prop4
