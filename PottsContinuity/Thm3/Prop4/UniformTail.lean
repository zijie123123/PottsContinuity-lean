module

public import Mathlib.Tactic

/-!
# Uniform weighted tail sums

A positive increasing weight converts a summable weighted series into a
uniform bound for each weighted tail. The unweighted tail is separately
proved summable; no nonsummable real-tsum convention is used.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Actual summability of every tail under a positive monotone weight. -/
theorem summable_tail_of_weighted (g w : ℕ → ℝ) (hg : ∀ m, 0 ≤ g m)
    (hw : Monotone w) (hweighted : Summable (fun m => w m*g m))
    (n : ℕ) (hwn : 0 < w n) : Summable (fun m : {m : ℕ // n ≤ m} => g m.1) := by
  have hs := (hweighted.subtype (fun m => n ≤ m)).div_const (w n)
  apply hs.of_nonneg_of_le (fun m => hg m.1)
  intro m
  apply (le_div_iff₀ hwn).mpr
  simpa only [mul_comm, Function.comp_def] using mul_le_mul_of_nonneg_right (hw m.2) (hg m.1)

/-- Each weighted tail is bounded by the total weighted series. -/
theorem weighted_tail_le_tsum (g w : ℕ → ℝ) (hg : ∀ m, 0 ≤ g m)
    (hw0 : ∀ m, 0 ≤ w m) (hw : Monotone w)
    (hweighted : Summable (fun m => w m*g m)) (n : ℕ) :
    w n*(∑' m : {m : ℕ // n ≤ m}, g m.1) ≤ ∑' m : ℕ, w m*g m := by
  classical
  rw [← tsum_mul_left]
  apply Real.tsum_le_of_sum_le (f := fun m : {m : ℕ // n ≤ m} => w n*g m.1)
    (fun m => mul_nonneg (hw0 n) (hg m.1))
  intro S
  let e : {m : ℕ // n ≤ m} ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  calc
    (∑ m ∈ S, w n*g m.1) ≤ ∑ m ∈ S, w m.1*g m.1 :=
      Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_right (hw m.2) (hg m.1))
    _ = ∑ m ∈ S.map e, w m*g m := by simp only [Finset.sum_map]; rfl
    _ ≤ ∑' m : ℕ, w m*g m :=
      hweighted.sum_le_tsum _ (fun m _ => mul_nonneg (hw0 m) (hg m))

end PottsContinuity.Thm3.Prop4
