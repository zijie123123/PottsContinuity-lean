module

public import PottsContinuity.BD12.EmbeddingPartition
public import Mathlib.Tactic

/-! Adding the unrevealed outer edges to a covariance sum is legitimate:
FKG makes every added covariance nonnegative under the original law. -/

@[expose] public section

namespace PottsContinuity.BD12
noncomputable section
variable {E O : Type*} [Fintype E] [DecidableEq E] [Fintype O] [DecidableEq O]

theorem finitePositiveCovariance_edge_nonneg
    (w : Finset O → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (f : Finset O → ℝ) (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) (a : O) :
    0 ≤ finitePositiveCovariance w f (fun A => if a ∈ A then 1 else 0) := by
  refine finitePositiveCovariance_nonneg w hw f _ hf0 ?_ hf ?_
  · intro A; split_ifs <;> norm_num
  · intro A B hAB
    by_cases ha : a ∈ A
    · simp only [ite_eq_left ha, ite_eq_left (hAB ha), le_refl]
    · simp only [ite_eq_right ha]; split_ifs <;> norm_num

omit [DecidableEq E] in
/-- Inner-edge covariances are bounded by the sum over all outer edges.
The observable remains the same actual outer observable throughout. -/
theorem finite_embedded_covariance_sum_le
    (i : E ↪ O) (w : Finset O → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (f : Finset O → ℝ) (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    (∑ a : E, finitePositiveCovariance w f (fun A => if i a ∈ A then 1 else 0)) ≤
      ∑ b : O, finitePositiveCovariance w f (fun A => if b ∈ A then 1 else 0) := by
  let c := fun b => finitePositiveCovariance w f (fun A => if b ∈ A then (1 : ℝ) else 0)
  change (∑ a : E, c (i a)) ≤ ∑ b : O, c b
  calc
    _ = ∑ b ∈ Finset.univ.image i, c b :=
      (Finset.sum_image (fun a _ b _ hab => i.injective hab)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun b _ _ => finitePositiveCovariance_edge_nonneg w hw f hf0 hf b)

end
end PottsContinuity.BD12
