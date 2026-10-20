module

public import PottsContinuity.BD12.FinitePinnedLaw

/-! Means and covariances of strictly positive finite weights, including true
inner-edge marginals, without requiring the marginal itself to be an FK law. -/

@[expose] public section

namespace PottsContinuity.BD12
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

abbrev finitePositiveMean (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ) : ℝ :=
  finitePinnedMean w ∅ ∅ f

def finitePositiveCovariance (w : Finset E → Set.Ioi (0 : ℝ))
    (f g : Finset E → ℝ) : ℝ :=
  finitePositiveMean w (fun A => f A * g A) - finitePositiveMean w f * finitePositiveMean w g

theorem finitePositiveMean_nonneg (w : Finset E → Set.Ioi (0 : ℝ))
    (f : Finset E → ℝ) (hf : ∀ A, 0 ≤ f A) : 0 ≤ finitePositiveMean w f := by
  unfold finitePositiveMean
  rw [finitePinnedMean_eq_sum_law]
  exact Finset.sum_nonneg (fun A _ => mul_nonneg ENNReal.toReal_nonneg (hf A))

theorem finitePositiveMean_mono (w : Finset E → Set.Ioi (0 : ℝ))
    (f g : Finset E → ℝ) (hfg : ∀ A, f A ≤ g A) :
    finitePositiveMean w f ≤ finitePositiveMean w g := by
  simp only [finitePositiveMean, finitePinnedMean_eq_sum_law]
  exact Finset.sum_le_sum (fun A _ => mul_le_mul_of_nonneg_left (hfg A) ENNReal.toReal_nonneg)

theorem finitePositiveMean_one (w : Finset E → Set.Ioi (0 : ℝ)) :
    finitePositiveMean w (fun _ => 1) = 1 := by
  unfold finitePositiveMean finitePinnedMean
  simp only [mul_one]
  exact div_self (finitePinnedPartition_pos w ∅ ∅).ne'

theorem finitePositiveCovariance_nonneg (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (f g : Finset E → ℝ) (hf0 : ∀ A, 0 ≤ f A) (hg0 : ∀ A, 0 ≤ g A)
    (hf : Monotone f) (hg : Monotone g) : 0 ≤ finitePositiveCovariance w f g :=
  sub_nonneg.mpr (finitePinnedMean_positive_association w hw ∅ ∅ f g hf0 hg0 hf hg)

end
end PottsContinuity.BD12
