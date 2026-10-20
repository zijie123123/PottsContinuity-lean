module

public import Mathlib.Tactic

/-! The numerical uniform-scale induction in KST: adjacent quasi-crossings,
cascade and closing transport a positive base bridge to every larger scale. -/

@[expose] public section

namespace PottsContinuity.BD12

/-- Induct beyond the last bridge above delta. The hypotheses are the exact
numerical adjacent, cascading and closing relations, not a final RSW bound. -/
theorem kst_uniform_scale_bridge_lower_bound
    (b : ℕ → ℝ) (Q : ℕ → ℕ → ℝ) (r δ : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hδ : 0 < δ) (hδr : 2*δ ≤ r^2)
    (hbase : δ ≤ b 0)
    (hadjacent : ∀ N, r ≤ Q (N+1) N)
    (hcascade : ∀ N m, m < N → 0 < Q N m →
      r ≤ max (Q (N+1) m) ((1-(1-b N)^2)/Q N m))
    (hclosing : ∀ N m, m ≤ N → Q N m * b m ≤ b N) :
    ∀ N, r*δ ≤ b N := by
  have hreach : ∀ N, b N < δ → ∃ m, m < N ∧ δ ≤ b m ∧ r ≤ Q N m := by
    intro N
    induction N with
    | zero => intro h; exact (not_lt_of_ge hbase h).elim
    | succ N ih =>
      intro hsmall
      by_cases hgood : δ ≤ b N
      · exact ⟨N,Nat.lt_succ_self N,hgood,hadjacent N⟩
      · obtain ⟨m,hm,hbm,hQ⟩ := ih (lt_of_not_ge hgood)
        have hQpos : 0 < Q N m := hr.trans_le hQ
        have hC := hcascade N m hm hQpos
        have hsecond : (1-(1-b N)^2)/Q N m < r := by
          apply (div_lt_iff₀ hQpos).mpr
          have hprod : r*r ≤ r*Q N m := mul_le_mul_of_nonneg_left hQ hr.le
          have hb : b N < δ := lt_of_not_ge hgood
          nlinarith only [hprod,hb,hδr,sq_nonneg (b N)]
        have hnext : r ≤ Q (N+1) m :=
          (le_max_iff.mp hC).resolve_right (not_le.mpr hsecond)
        exact ⟨m,hm.trans (Nat.lt_succ_self N),hbm,hnext⟩
  intro N
  by_cases hgood : δ ≤ b N
  · exact (mul_le_of_le_one_left hδ.le hr1).trans hgood
  · obtain ⟨m,hm,hbm,hQ⟩ := hreach N (lt_of_not_ge hgood)
    exact (mul_le_mul hQ hbm hδ.le (hr.le.trans hQ)).trans (hclosing N m hm.le)

/-- A positive base bridge and uniform quasi-crossing relations give a
positive lower bound independent of scale. -/
theorem kst_exists_uniform_bridge_lower_bound
    (b : ℕ → ℝ) (Q : ℕ → ℕ → ℝ) (r : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hbase : 0 < b 0)
    (hadjacent : ∀ N, r ≤ Q (N+1) N)
    (hcascade : ∀ N m, m < N → 0 < Q N m →
      r ≤ max (Q (N+1) m) ((1-(1-b N)^2)/Q N m))
    (hclosing : ∀ N m, m ≤ N → Q N m * b m ≤ b N) :
    ∃ c : ℝ, 0 < c ∧ ∀ N, c ≤ b N := by
  let δ := min (b 0) (r^2/4)
  have hδ : 0 < δ := lt_min hbase (div_pos (sq_pos_of_pos hr) (by norm_num))
  refine ⟨r*δ,mul_pos hr hδ,?_⟩
  apply kst_uniform_scale_bridge_lower_bound b Q r δ hr hr1 hδ _ (min_le_left _ _)
    hadjacent hcascade hclosing
  have h := min_le_right (b 0) (r^2/4)
  change 2 * min (b 0) (r^2/4) ≤ r^2
  nlinarith only [h,sq_nonneg r]

end PottsContinuity.BD12
