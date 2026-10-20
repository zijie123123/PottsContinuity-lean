module

public import PottsContinuity.Thm3.Push.StripCaseOneLimit

@[expose] public section

namespace PottsContinuity.Push
open PD.FK RSW MeasureTheory

/-- The exact rounded local constant used by all-scale Lemma 2, obtained in
Case 1 from the two actual strip arm bounds at EVERY n>=9. -/
theorem strip_rounded_case_one_stripLocalLower
    (q : Set.Ici (1:ℝ)) (k n : ℕ) (hk : 1 ≤ k) (hn : 9 ≤ n) (x : ℤ)
    (hfirst : (1/(36*(k:ℝ)))/3 ≤
      (selfDualStripMeasure q n).real (stripCaseOneFirstArm n ((n+8)/9) x))
    (hsecond : (1/(36*(k:ℝ)))/3 ≤
      (selfDualStripMeasure q n).real (stripCaseOneSecondArm n ((n+8)/9) x)) :
    stripLocalLower q k ≤
      (selfDualStripMeasure q n).real (stripLocalConnection n ((n+8)/9) x) := by
  obtain ⟨hs,_,hcap⟩ := strip_ceil_ninth_spacing n (by omega)
  have h := strip_intervalArm_case_one_lower_bound q n ((n+8)/9) hs (by omega) x
    (1/(36*(k:ℝ))) (by positivity) hfirst hsecond
  apply le_trans _ h
  unfold stripLocalLower
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  nlinarith [sq_nonneg (q:ℝ)]

end PottsContinuity.Push
