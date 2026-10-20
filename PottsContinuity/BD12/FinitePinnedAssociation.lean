module

public import Mathlib.Combinatorics.SetFamily.FourFunctions
public import Mathlib.Tactic

/-! Finite conditional FKG for positive weights on the Boolean cube.
Pinning is literal restriction to configurations agreeing on the revealed
coordinates. Its zero density off that event is the actual conditional density. -/

@[expose] public section

namespace PottsContinuity.BD12

open scoped BigOperators
noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Unnormalized density after revealing exactly the coordinates in R. -/
def finitePinnedWeight (w : Finset E → Set.Ioi (0 : ℝ)) (R H A : Finset E) : ℝ :=
  if A ∩ R = H ∩ R then (w A : ℝ) else 0

omit [Fintype E] in
theorem finitePinnedWeight_nonneg (w : Finset E → Set.Ioi (0 : ℝ))
    (R H A : Finset E) : 0 ≤ finitePinnedWeight w R H A := by
  unfold finitePinnedWeight
  split_ifs
  · exact (w A).property.le
  · exact le_rfl

theorem finitePinnedPartition_pos (w : Finset E → Set.Ioi (0 : ℝ))
    (R H : Finset E) : 0 < ∑ A, finitePinnedWeight w R H A := by
  apply Finset.sum_pos' (fun A _ => finitePinnedWeight_nonneg w R H A)
  refine ⟨H, Finset.mem_univ H, ?_⟩
  have hwH : (0 : ℝ) < w H := (w H).property
  simpa only [finitePinnedWeight, ite_true] using hwH

/-- Conditional expectation under the normalized positive finite law.
Every pattern H on every reveal set R has strictly positive probability. -/
def finitePinnedMean (w : Finset E → Set.Ioi (0 : ℝ)) (R H : Finset E)
    (f : Finset E → ℝ) : ℝ :=
  (∑ A, finitePinnedWeight w R H A * f A) / ∑ A, finitePinnedWeight w R H A

omit [Fintype E] in
theorem finitePinnedWeight_lattice_condition (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (R H A B : Finset E) :
    finitePinnedWeight w R H A * finitePinnedWeight w R H B ≤
      finitePinnedWeight w R H (A ∩ B) * finitePinnedWeight w R H (A ∪ B) := by
  by_cases hA : A ∩ R = H ∩ R
  · by_cases hB : B ∩ R = H ∩ R
    · have hi : (A ∩ B) ∩ R = H ∩ R := by
        rw [Finset.inter_assoc, hB, ← hA]
        simp only [← Finset.inter_assoc, Finset.inter_self]
      have hu : (A ∪ B) ∩ R = H ∩ R := by
        rw [Finset.union_inter_distrib_right, hA, hB, Finset.union_self]
      simpa only [finitePinnedWeight, ite_eq_left hA, ite_eq_left hB, ite_eq_left hi, ite_eq_left hu]
        using hw A B
    · simp only [finitePinnedWeight, ite_eq_right hB, mul_zero]
      exact mul_nonneg (finitePinnedWeight_nonneg w R H (A ∩ B))
        (finitePinnedWeight_nonneg w R H (A ∪ B))
  · simp only [finitePinnedWeight, ite_eq_right hA, zero_mul]
    exact mul_nonneg (finitePinnedWeight_nonneg w R H (A ∩ B))
      (finitePinnedWeight_nonneg w R H (A ∪ B))

/-- Conditional positive association, for every reveal set and every pattern.
This is one of the monotonicity inputs to DRT's adaptive sampler. -/
theorem finitePinnedMean_positive_association (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (R H : Finset E) (f g : Finset E → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hg0 : ∀ A, 0 ≤ g A)
    (hf : Monotone f) (hg : Monotone g) :
    finitePinnedMean w R H f * finitePinnedMean w R H g ≤
      finitePinnedMean w R H (fun A => f A * g A) := by
  have h := _root_.fkg (μ := finitePinnedWeight w R H) (f := f) (g := g)
    (finitePinnedWeight_nonneg w R H) hf0 hg0 hf hg
    (finitePinnedWeight_lattice_condition w hw R H)
  have hz := finitePinnedPartition_pos w R H
  unfold finitePinnedMean
  calc
    _ = ((∑ A, finitePinnedWeight w R H A * f A) *
      (∑ A, finitePinnedWeight w R H A * g A)) /
        ((∑ A, finitePinnedWeight w R H A) * ∑ A, finitePinnedWeight w R H A) :=
      div_mul_div_comm _ _ _ _
    _ ≤ ((∑ A, finitePinnedWeight w R H A) *
        ∑ A, finitePinnedWeight w R H A * (f A * g A)) /
        ((∑ A, finitePinnedWeight w R H A) * ∑ A, finitePinnedWeight w R H A) :=
      div_le_div_of_nonneg_right h (mul_pos hz hz).le
    _ = _ := by field_simp

end
end PottsContinuity.BD12
