module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic

/-! Exact multiplicity bound for integer halving in the source partial-sum
comparison, with the radius-zero term retained. -/

@[expose] public section

namespace PottsContinuity.BD12

/-- Each integer half-radius has at most two original radius indices. -/
theorem drt_halving_fibre_card_le_two (n j : ℕ) :
    ({k ∈ Finset.range n | k / 2 = j}).card ≤ 2 := by
  have hsub : {k ∈ Finset.range n | k / 2 = j} ⊆ ({2*j, 2*j+1} : Finset ℕ) := by
    intro k hk
    have heq := (Finset.mem_filter.mp hk).2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hcard : ({2*j, 2*j+1} : Finset ℕ).card ≤ 2 := by
    simp
  exact (Finset.card_le_card hsub).trans hcard

/-- Halving indices costs at most twice the first n terms of any nonnegative sequence. -/
theorem drt_sum_halved_le_twice (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (n : ℕ) :
    (∑ k ∈ Finset.range n, b (k / 2)) ≤ 2 * ∑ j ∈ Finset.range n, b j := by
  have hmaps : ∀ k ∈ Finset.range n, k / 2 ∈ Finset.range n := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps b]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (hb j)
  exact_mod_cast drt_halving_fibre_card_le_two n j

end PottsContinuity.BD12
