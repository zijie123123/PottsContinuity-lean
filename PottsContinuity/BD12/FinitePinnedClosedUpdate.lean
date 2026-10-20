module

public import PottsContinuity.BD12.FinitePinnedMonotonicity

/-! Closed-coordinate conditioning and the conditional open/closed comparison
used by a monotone adaptive sampler. -/

@[expose] public section

namespace PottsContinuity.BD12

open scoped BigOperators
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] in
theorem finitePinnedWeight_closed_update (w : Finset E → Set.Ioi (0 : ℝ))
    (R H A : Finset E) (e : E) (he : e ∉ R) :
    finitePinnedWeight w (insert e R) (H.erase e) A =
      finitePinnedWeight w R H A * (if e ∈ A then 0 else 1) := by
  have hiff : A ∩ insert e R = H.erase e ∩ insert e R ↔
      e ∉ A ∧ A ∩ R = H ∩ R := by
    constructor
    · intro h
      have heA : e ∉ A := by
        intro hm
        have hx : e ∈ H.erase e ∩ insert e R := by rw [← h]; simp [hm]
        exact Finset.notMem_erase e H (Finset.mem_inter.mp hx).1
      refine ⟨heA, ?_⟩
      ext x
      by_cases hx : x = e
      · subst x
        simp [he]
      · have hm := Finset.ext_iff.mp h x
        simpa only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase,
          hx, false_or, ne_eq, not_false_eq_true, true_and] using hm
    · rintro ⟨heA, h⟩
      ext x
      by_cases hx : x = e
      · subst x
        simp [heA]
      · have hm := Finset.ext_iff.mp h x
        simpa only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase,
          hx, false_or, ne_eq, not_false_eq_true, true_and] using hm
  unfold finitePinnedWeight
  simp only [hiff]
  by_cases ha : e ∈ A <;> by_cases hr : A ∩ R = H ∩ R <;> simp [ha, hr]

omit [Fintype E] in
theorem finitePinnedWeight_closed_add_open (w : Finset E → Set.Ioi (0 : ℝ))
    (R H A : Finset E) (e : E) (he : e ∉ R) :
    finitePinnedWeight w (insert e R) (H.erase e) A +
      finitePinnedWeight w (insert e R) (insert e H) A = finitePinnedWeight w R H A := by
  rw [finitePinnedWeight_closed_update w R H A e he,
    finitePinnedWeight_open_update w R H A e he]
  by_cases ha : e ∈ A <;> simp [ha]

/-- Revealing a closed coordinate decreases every increasing nonnegative
observable; this is derived from conditional FKG, not assumed. -/
theorem finitePinnedMean_closed_update_le (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (R H : Finset E) (e : E) (he : e ∉ R) (f : Finset E → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    finitePinnedMean w (insert e R) (H.erase e) f ≤ finitePinnedMean w R H f := by
  have hg0 : ∀ A : Finset E, (0 : ℝ) ≤ if e ∈ A then 1 else 0 := by
    intro A
    split_ifs <;> norm_num
  have hg : Monotone (fun A : Finset E => if e ∈ A then (1 : ℝ) else 0) := by
    intro A B hAB
    by_cases ha : e ∈ A
    · simp [ha, hAB ha]
    · simp only [ite_eq_right ha]
      exact hg0 B
  have h := _root_.fkg (μ := finitePinnedWeight w R H) (f := f)
    (g := fun A => if e ∈ A then 1 else 0)
    (finitePinnedWeight_nonneg w R H) hf0 hg0 hf hg
    (finitePinnedWeight_lattice_condition w hw R H)
  have hden : (∑ A, finitePinnedWeight w (insert e R) (H.erase e) A) +
      (∑ A, finitePinnedWeight w (insert e R) (insert e H) A) =
      ∑ A, finitePinnedWeight w R H A := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun A _ => finitePinnedWeight_closed_add_open w R H A e he)
  have hnum : (∑ A, finitePinnedWeight w (insert e R) (H.erase e) A * f A) +
      (∑ A, finitePinnedWeight w (insert e R) (insert e H) A * f A) =
      ∑ A, finitePinnedWeight w R H A * f A := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro A _
    rw [← add_mul, finitePinnedWeight_closed_add_open w R H A e he]
  have hopen (A : Finset E) :
      finitePinnedWeight w R H A * (f A * (if e ∈ A then 1 else 0)) =
        finitePinnedWeight w (insert e R) (insert e H) A * f A := by
    rw [finitePinnedWeight_open_update w R H A e he]
    ring
  simp_rw [← finitePinnedWeight_open_update w R H _ e he, hopen] at h
  unfold finitePinnedMean
  apply (div_le_div_iff₀ (finitePinnedPartition_pos w (insert e R) (H.erase e))
    (finitePinnedPartition_pos w R H)).mpr
  rw [← hden, ← hnum] at h ⊢
  nlinarith only [h]

theorem finitePinnedMean_closed_le_open (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (R H : Finset E) (e : E) (he : e ∉ R) (f : Finset E → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    finitePinnedMean w (insert e R) (H.erase e) f ≤
      finitePinnedMean w (insert e R) (insert e H) f :=
  (finitePinnedMean_closed_update_le w hw R H e he f hf0 hf).trans
    (finitePinnedMean_le_open_update w hw R H e he f hf0 hf)

end
end PottsContinuity.BD12
