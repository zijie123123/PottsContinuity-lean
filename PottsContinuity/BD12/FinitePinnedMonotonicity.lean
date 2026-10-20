module

public import PottsContinuity.BD12.FinitePinnedAssociation

/-! Revealing an open coordinate increases every increasing nonnegative
observable under a positive log-supermodular finite Boolean law. -/

@[expose] public section

namespace PottsContinuity.BD12

open scoped BigOperators
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] in
theorem finitePinnedWeight_open_update (w : Finset E → Set.Ioi (0 : ℝ))
    (R H A : Finset E) (e : E) (he : e ∉ R) :
    finitePinnedWeight w (insert e R) (insert e H) A =
      finitePinnedWeight w R H A * (if e ∈ A then 1 else 0) := by
  have hiff : A ∩ insert e R = insert e H ∩ insert e R ↔
      e ∈ A ∧ A ∩ R = H ∩ R := by
    constructor
    · intro h
      have heA : e ∈ A := by
        have hm : e ∈ A ∩ insert e R := by rw [h]; simp
        exact (Finset.mem_inter.mp hm).1
      refine ⟨heA, ?_⟩
      ext x
      by_cases hx : x = e
      · subst x
        simp [he]
      · have hm := Finset.ext_iff.mp h x
        simpa only [Finset.mem_inter, Finset.mem_insert, hx, false_or] using hm
    · rintro ⟨heA, h⟩
      ext x
      by_cases hx : x = e
      · subst x
        simp [heA]
      · have hm := Finset.ext_iff.mp h x
        simpa only [Finset.mem_inter, Finset.mem_insert, hx, false_or] using hm
  unfold finitePinnedWeight
  simp only [hiff]
  by_cases ha : e ∈ A <;> by_cases hr : A ∩ R = H ∩ R <;> simp [ha, hr]

theorem finitePinnedMean_open_update (w : Finset E → Set.Ioi (0 : ℝ))
    (R H : Finset E) (e : E) (he : e ∉ R) (f : Finset E → ℝ) :
    finitePinnedMean w (insert e R) (insert e H) f =
      finitePinnedMean w R H (fun A => f A * (if e ∈ A then 1 else 0)) /
        finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0) := by
  unfold finitePinnedMean
  simp_rw [finitePinnedWeight_open_update w R H _ e he]
  rw [div_div_div_cancel_right₀ (finitePinnedPartition_pos w R H).ne']
  congr 1
  apply Finset.sum_congr rfl
  intro A _
  ring

theorem finitePinnedMean_open_probability_pos (w : Finset E → Set.Ioi (0 : ℝ))
    (R H : Finset E) (e : E) (he : e ∉ R) :
    0 < finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0) := by
  apply div_pos _ (finitePinnedPartition_pos w R H)
  have h := finitePinnedPartition_pos w (insert e R) (insert e H)
  simpa only [finitePinnedWeight_open_update w R H _ e he] using h

/-- The one-step conditional monotonicity required by the monotone sampler.
No conditional association or influence estimate is assumed. -/
theorem finitePinnedMean_le_open_update (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (R H : Finset E) (e : E) (he : e ∉ R) (f : Finset E → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    finitePinnedMean w R H f ≤ finitePinnedMean w (insert e R) (insert e H) f := by
  have hg0 : ∀ A : Finset E, (0 : ℝ) ≤ if e ∈ A then 1 else 0 := by
    intro A
    split_ifs <;> norm_num
  have hg : Monotone (fun A : Finset E => if e ∈ A then (1 : ℝ) else 0) := by
    intro A B hAB
    by_cases ha : e ∈ A
    · simp [ha, hAB ha]
    · simp only [ite_eq_right ha]
      exact hg0 B
  have h := finitePinnedMean_positive_association w hw R H f
    (fun A => if e ∈ A then 1 else 0) hf0 hg0 hf hg
  rw [finitePinnedMean_open_update w R H e he f]
  exact (le_div_iff₀ (finitePinnedMean_open_probability_pos w R H e he)).mpr h

end
end PottsContinuity.BD12
