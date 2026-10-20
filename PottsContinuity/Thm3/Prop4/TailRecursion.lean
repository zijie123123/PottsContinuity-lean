module

public import PottsContinuity.Thm3.Prop4.Recursion
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real

/-!
# Truncating a monotone tail-envelope recursion

DCST (15 May 2015), TeX lines 1793–1821. The sequence and attained product
witnesses are explicit numeric inputs. Attainment of tail suprema is proved in
`Thm3.Prop4.TailEnvelope` (`convergentTailSup_attained`); the attained recursion is
derived from the summation bound in `Thm3.Prop4.SummationDecay`
(`exponential_tail_of_summationBound`) and applied to the one-arm probability in
`Thm3.Prop4.EvenSquareDecay`.
-/

@[expose] public section

open Filter Topology

namespace PottsContinuity.Thm3.Prop4

/-- Once the tail is below one, a positive term cannot be bounded by a product
with either index beyond it. For a zero term we supply valid smaller indices. -/
theorem truncate_product_witness (Q : ℕ → ℝ) (hQ : ∀ n, 0 ≤ Q n)
    (hanti : Antitone Q) (n r : ℕ) (hn : 2 ≤ n) (hr : r < n)
    (hrQ : Q r < 1)
    (hw : ∃ k l : ℕ, r ≤ k ∧ r ≤ l ∧ n ≤ k + l ∧ Q n ≤ Q k * Q l) :
    ∃ k l : ℕ, r ≤ k ∧ k < n ∧ r ≤ l ∧ l < n ∧ n ≤ k + l ∧
      Q n ≤ Q k * Q l := by
  by_cases hzero : Q n = 0
  · refine ⟨n-1, n-1, by omega, by omega, by omega, by omega, by omega, ?_⟩
    rw [hzero]
    exact mul_nonneg (hQ _) (hQ _)
  · have hnQ : 0 < Q n := lt_of_le_of_ne (hQ n) (Ne.symm hzero)
    obtain ⟨k, l, hk, hl, hsum, hprod⟩ := hw
    have hkn : k < n := by
      by_contra h
      have hkQ := hanti (Nat.le_of_not_gt h)
      have hlQ : Q l < 1 := (hanti hl).trans_lt hrQ
      have hmul := mul_le_mul_of_nonneg_right hkQ (hQ l)
      nlinarith only [hprod, hmul, hnQ, hlQ]
    have hln : l < n := by
      by_contra h
      have hlQ := hanti (Nat.le_of_not_gt h)
      have hkQ : Q k < 1 := (hanti hk).trans_lt hrQ
      have hmul := mul_le_mul_of_nonneg_left hlQ (hQ k)
      nlinarith only [hprod, hmul, hnQ, hkQ]
    exact ⟨k, l, hk, hkn, hl, hln, hsum, hprod⟩

/-- A nonnegative antitone sequence tending to zero and obeying an attained
product recursion decays exponentially on a tail. Any diverging index cutoff
works, including the corrected half-scale cutoff. -/
theorem exponential_tail_of_product_recursion
    (Q : ℕ → ℝ) (r : ℕ → ℕ)
    (hQ : ∀ n, 0 ≤ Q n) (hanti : Antitone Q)
    (hlim : Tendsto Q atTop (𝓝 0)) (hrlim : Tendsto r atTop atTop)
    (hrlt : ∀ᶠ n in atTop, r n < n)
    (hrec : ∀ n, 1 ≤ n →
      ∃ k l : ℕ, r n ≤ k ∧ r n ≤ l ∧ n ≤ k + l ∧ Q n ≤ Q k * Q l) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, Q n ≤ Real.exp (-c * (n : ℝ)) := by
  have hsmall : ∀ᶠ n in atTop, Q n < 1 := hlim.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hsmall
  let M := max 1 M₀
  have hsmallM : ∀ n, M ≤ n → Q n < 1 := by
    intro n hn
    exact hM₀ n (le_trans (le_max_right 1 M₀) hn)
  have hcut : ∀ᶠ n in atTop, M ≤ r n := hrlim.eventually (eventually_ge_atTop M)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hcut.and (hrlt.and (eventually_ge_atTop 2)))
  obtain ⟨c, hc, hbound⟩ := exponential_bound_of_truncated_product_recursion Q M N
    (le_max_left _ _) hQ (fun n hn _ => hsmallM n hn) (by
      intro n hn _
      obtain ⟨hMr, hrn, hn2⟩ := hN n hn.le
      obtain ⟨k, l, hk, hkn, hl, hln, hsum, hprod⟩ :=
        truncate_product_witness Q hQ hanti n (r n) hn2 hrn (hsmallM _ hMr)
          (hrec n (by omega))
      exact ⟨k, l, hMr.trans hk, hkn, hMr.trans hl, hln, hsum, hprod⟩)
  refine ⟨c, hc, ?_⟩
  exact (eventually_ge_atTop M).mono (fun n hn => hbound n hn)

end PottsContinuity.Thm3.Prop4
