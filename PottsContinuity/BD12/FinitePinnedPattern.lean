module

public import PottsContinuity.BD12.FinitePinnedClosedUpdate
public import Mathlib.Data.Finset.Interval

/-! Monotonicity in every revealed coordinate, rather than just a single
open/closed comparison. This supplies DRT's finite monotonic-measure property. -/

@[expose] public section

namespace PottsContinuity.BD12

noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

theorem finitePinnedMean_pattern_congr (w : Finset E → Set.Ioi (0 : ℝ))
    (R H K : Finset E) (h : H ∩ R = K ∩ R) (f : Finset E → ℝ) :
    finitePinnedMean w R H f = finitePinnedMean w R K f := by
  simp only [finitePinnedMean, finitePinnedWeight, h]

/-- Every conditional increasing expectation is monotone in the entire
revealed pattern. Values outside the revealed set have no effect. -/
theorem finitePinnedMean_monotone_pattern (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (R : Finset E) (f : Finset E → ℝ) (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    Monotone (fun H => finitePinnedMean w R H f) := by
  apply Finset.monotone_iff_forall_le_insert.mpr
  intro H e heH
  by_cases heR : e ∈ R
  · have h := finitePinnedMean_closed_le_open w hw (R.erase e) H e
      (Finset.notMem_erase e R) f hf0 hf
    simpa only [Finset.insert_erase heR, Finset.erase_eq_of_notMem heH] using h
  · exact (finitePinnedMean_pattern_congr w R H (insert e H)
      (Finset.insert_inter_of_notMem heR).symm f).le

/-- In particular, every single-coordinate conditional open probability is
monotone in the past revealed values, as required by the sequential sampler. -/
theorem finitePinnedOpenProbability_monotone (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (R : Finset E) (e : E) :
    Monotone (fun H => finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0)) := by
  apply finitePinnedMean_monotone_pattern w hw R
  · intro A
    split_ifs <;> norm_num
  · intro A B hAB
    by_cases ha : e ∈ A
    · simp [ha, hAB ha]
    · simp only [ite_eq_right ha]
      split_ifs <;> norm_num

end
end PottsContinuity.BD12
