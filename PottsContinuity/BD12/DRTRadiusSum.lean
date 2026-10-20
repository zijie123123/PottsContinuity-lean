module

public import Mathlib.Data.Nat.Dist
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic

/-! The factor-two shell-radius counting step in DRT's corollary of the OSSS inequality. -/

@[expose] public section

namespace PottsContinuity.BD12

/-- At most two integer shell indices have a given distance to an integer
radius. The endpoints of the ambient interval do not affect this bound. -/
theorem drt_radius_distance_fibre_card_le_two (n d j : ℕ) :
    ({k ∈ Finset.Icc 1 n | Nat.dist k d = j}).card ≤ 2 := by
  have hsub : {k ∈ Finset.Icc 1 n | Nat.dist k d = j} ⊆ ({d - j, d + j} : Finset ℕ) := by
    intro k hk
    have heq := (Finset.mem_filter.mp hk).2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    unfold Nat.dist at heq
    omega
  have hcard : ({d - j, d + j} : Finset ℕ).card ≤ 2 := by
    by_cases heq : d - j = d + j <;> simp [heq]
  exact (Finset.card_le_card hsub).trans hcard

/-- For a decreasing nonnegative one-arm sequence, summing the shell-distance
bounds over k=1,...,n costs at most twice its first n terms. The d=0 endpoint
case is handled by monotonicity, rather than dropping the radius n term. -/
theorem drt_radius_sum_le_twice_partial_sum (a : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (n d : ℕ) (hd : d ≤ n) :
    (∑ k ∈ Finset.Icc 1 n, a (Nat.dist k d)) ≤ 2 * ∑ j ∈ Finset.range n, a j := by
  by_cases hd0 : d = 0
  · subst d
    simp_rw [Nat.dist_zero_right]
    have hset : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hset, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    have hs : (∑ k ∈ Finset.range n, a (1 + k)) ≤ ∑ k ∈ Finset.range n, a k :=
      Finset.sum_le_sum (fun k _ => hmono (by omega))
    have hnonneg : 0 ≤ ∑ k ∈ Finset.range n, a k := Finset.sum_nonneg (fun k _ => ha k)
    linarith only [hs, hnonneg]
  have hmaps : ∀ k ∈ Finset.Icc 1 n, Nat.dist k d ∈ Finset.range n := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    rw [Finset.mem_range]
    unfold Nat.dist
    omega
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps a]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (ha j)
  exact_mod_cast drt_radius_distance_fibre_card_le_two n d j

end PottsContinuity.BD12
