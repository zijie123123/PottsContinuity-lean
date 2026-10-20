module

public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real

/-!
# The numeric final induction of Proposition 4

DCST (15 May 2015), TeX lines 1793–1822. These are lemmas about real sequences,
with no model-specific input. The truncated product recursion for the tail
envelope Q_n=C*sup_{m≥n}u_m is derived from an attained recursion for u in
`Thm3.Prop4.TailEnvelope` (`envelope_product_recursion_of_attainedRecursion`,
truncated by `Thm3.Prop4.TailRecursion`), and is applied to the random-cluster
one-arm probability in `Thm3.Prop4.EvenSquareDecay`. Finite base rates
are combined by minimum, correcting the printed maximum. Zeros are allowed.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- A sequence strictly below one on a finite set of positive indices admits
one positive exponential rate on that set, including when some values vanish. -/
theorem finite_exponential_rate (Q : ℕ → ℝ) (s : Finset ℕ)
    (h : ∀ n ∈ s, 1 ≤ n ∧ Q n < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n ∈ s, Q n ≤ Real.exp (-c * (n : ℝ)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert n s hns ih =>
    obtain ⟨d, hd, hds⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    have hn := h n (Finset.mem_insert_self n s)
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn.1
    let b : ℝ := max (Q n) (1 / 2)
    have hb : 0 < b := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hb1 : b < 1 := max_lt hn.2 (by norm_num)
    let e : ℝ := -Real.log b / (n : ℝ)
    have he : 0 < e := div_pos (neg_pos.mpr (Real.log_neg hb hb1)) hnR
    have hen : Q n ≤ Real.exp (-e * (n : ℝ)) := by
      have heq : -e * (n : ℝ) = Real.log b := by
        dsimp [e]
        field_simp
      rw [heq, Real.exp_log hb]
      exact le_max_left _ _
    refine ⟨min d e, lt_min hd he, ?_⟩
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hen.trans (Real.exp_le_exp.mpr (by
        nlinarith only [min_le_right d e, hnR]))
    · exact (hds k hk).trans (Real.exp_le_exp.mpr (by
        have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith only [min_le_left d e, hkR]))

/-- Strong induction from a truncated product recursion. The fixed lower
cutoff can be supplied by any increasing scale threshold; no specific choice
of the threshold, or model-specific recursion, is asserted here. -/
theorem exponential_bound_of_truncated_product_recursion
    (Q : ℕ → ℝ) (M N : ℕ) (hM : 1 ≤ M)
    (hQ : ∀ n, 0 ≤ Q n)
    (hbase : ∀ n, M ≤ n → n ≤ N → Q n < 1)
    (hrec : ∀ n, N < n → M ≤ n →
      ∃ k l : ℕ, M ≤ k ∧ k < n ∧ M ≤ l ∧ l < n ∧ n ≤ k + l ∧
        Q n ≤ Q k * Q l) :
    ∃ c : ℝ, 0 < c ∧ ∀ n, M ≤ n → Q n ≤ Real.exp (-c * (n : ℝ)) := by
  obtain ⟨c, hc, hcs⟩ := finite_exponential_rate Q (Finset.Icc M N) (by
    intro n hn
    obtain ⟨hm, hnN⟩ := Finset.mem_Icc.mp hn
    exact ⟨hM.trans hm, hbase n hm hnN⟩)
  refine ⟨c, hc, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hnN : n ≤ N
    · exact hcs n (Finset.mem_Icc.mpr ⟨hn, hnN⟩)
    · obtain ⟨k, l, hkM, hkn, hlM, hln, hsum, hprod⟩ :=
        hrec n (Nat.lt_of_not_ge hnN) hn
      calc
        Q n ≤ Q k * Q l := hprod
        _ ≤ Real.exp (-c * (k : ℝ)) * Real.exp (-c * (l : ℝ)) :=
          mul_le_mul (ih k hkn hkM) (ih l hln hlM) (hQ l)
            (le_of_lt (Real.exp_pos _))
        _ = Real.exp (-c * ((k + l : ℕ) : ℝ)) := by
          rw [← Real.exp_add, Nat.cast_add]
          congr 1
          ring
        _ ≤ Real.exp (-c * (n : ℝ)) := Real.exp_le_exp.mpr (by
          have hsumR : (n : ℝ) ≤ (k : ℝ) + l := by exact_mod_cast hsum
          rw [Nat.cast_add]
          nlinarith only [hc, hsumR])

end PottsContinuity.Thm3.Prop4
