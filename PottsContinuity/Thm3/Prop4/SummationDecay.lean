module

public import PottsContinuity.Thm3.Prop4.EvenRecursion
public import PottsContinuity.Thm3.Prop4.PowerCutoff
public import PottsContinuity.Thm3.Prop4.HalfScale
public import PottsContinuity.Thm3.Prop4.TailEnvelope
public import Mathlib.Tactic

/-!
# The complete numerical summation-to-decay argument

DCST, TeX lines 1775–1822, with the rounded half-scale cutoff and attained
maxima. The summation bound and the one-step ratio bound are hypotheses here;
for the one-arm probability they are supplied in `Thm3.Prop4.EvenSquareDecay` by
`reweighted_summation_of_evenSquarePairBound` and `oneArm_probability_upper_ratio`.
-/

@[expose] public section

open Filter Topology

namespace PottsContinuity.Thm3.Prop4

/-- The source summation estimate implies exponential decay for a generic
nonnegative zero-limit sequence with a one-step upper ratio. -/
theorem exponential_tail_of_summationBound (u : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hlim : Tendsto u atTop (𝓝 0))
    (C c ε β D : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hε : 0 < ε) (hεβ : ε < β) (hβ1 : β < 1) (hD : 1 ≤ D)
    (hratio : ∀ n, u n ≤ D*u (n+1))
    (hsum : ∀ n : ℕ, 1 ≤ n → u (2*n) ≤
      Real.exp (((2*n : ℕ) : ℝ)^β)*
        (∑' m : {m : ℕ // n ≤ m}, prop4ReweightedKernel C c ε β u m.1)) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ n in atTop, u n ≤ Real.exp (-d*(n : ℝ)) := by
  obtain ⟨K,hK,heven⟩ := even_product_recursion_of_summationBound u hu hlim
    C c ε β hC hc hε hεβ hβ1 hsum
  have hrounded : ∀ m, 1 ≤ m → ∃ k l : ℕ,
      powerCutoff ε m ≤ k ∧ powerCutoff ε m ≤ l ∧ 2*m ≤ k+l ∧
      u (2*m) ≤ K*u k*u l := by
    intro m hm
    obtain ⟨k,l,hk,hl,hkl,hb⟩ := heven m hm
    exact ⟨k,l,(powerCutoff_le_iff ε m k).mpr hk,
      (powerCutoff_le_iff ε m l).mpr hl,hkl,hb⟩
  let r : ℕ → ℕ := fun n => powerCutoff ε (n/2)
  have hr : Monotone r := fun n m hnm =>
    powerCutoff_monotone ε hε.le (Nat.div_le_div_right hnm)
  have hrlim : Tendsto r atTop atTop := (powerCutoff_tendsto ε hε).comp halfIndex_tendsto
  have hrec := all_index_recursion_half_scale_of_evenRecursion u hu (powerCutoff ε)
    (powerCutoff_monotone ε hε.le) K D hK hD hratio hrounded
  exact exponential_tail_of_attainedRecursion u hlim hu (D*K)
    (mul_pos (zero_lt_one.trans_le hD) hK) r hr hrlim
    (halfPowerCutoff_eventually_lt ε hε.le (hεβ.trans hβ1)) hrec

/-- Full positive-index numerical decay upgrade for the original sequence.
The corrected stretched-exponential coefficient is retained throughout. -/
theorem exponential_bound_of_reweightedSummation (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (α c₀ C c ε β D : ℝ)
    (hα : 0 < α) (hc₀ : 0 < c₀) (hC : 0 < C) (hc : 0 < c)
    (hε : 0 < ε) (hεβ : ε < β) (hβα : β < α) (hβ1 : β < 1)
    (hD : 1 ≤ D) (hratio : ∀ n, a n ≤ D*a (n+1))
    (hdecay : ∀ n, 1 ≤ n → a n ≤ Real.exp (-c₀*(n : ℝ)^α))
    (hsum : ∀ n : ℕ, 1 ≤ n →
      Real.exp (((2*n : ℕ) : ℝ)^β)*a (2*n) ≤
      Real.exp (((2*n : ℕ) : ℝ)^β)*
        (∑' m : {m : ℕ // n ≤ m}, prop4ReweightedKernel C c ε β
          (fun k => Real.exp ((k : ℝ)^β)*a k) m.1)) :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℕ, 1 ≤ n → a n ≤ Real.exp (-d*(n : ℝ)) := by
  let u : ℕ → ℝ := fun n => Real.exp ((n : ℝ)^β)*a n
  have hu : ∀ n, 0 ≤ u n := fun n => mul_nonneg (Real.exp_nonneg _) (ha n)
  have hlim : Tendsto u atTop (𝓝 0) :=
    weighted_stretched_exponential_tendsto_zero a hα hβα hc₀ ha hdecay
  have hratioU : ∀ n, u n ≤ D*u (n+1) := by
    intro n
    have he : Real.exp ((n : ℝ)^β) ≤ Real.exp (((n+1 : ℕ) : ℝ)^β) :=
      Real.exp_le_exp.mpr (Real.rpow_le_rpow (Nat.cast_nonneg n)
        (by exact_mod_cast Nat.le_succ n) (hε.trans hεβ).le)
    calc
      u n ≤ Real.exp ((n : ℝ)^β)*(D*a (n+1)) :=
        mul_le_mul_of_nonneg_left (hratio n) (Real.exp_nonneg _)
      _ ≤ Real.exp (((n+1 : ℕ) : ℝ)^β)*(D*a (n+1)) :=
        mul_le_mul_of_nonneg_right he (mul_nonneg (zero_le_one.trans hD) (ha _))
      _ = D*u (n+1) := by dsimp [u]; ring
  obtain ⟨d,hd,hbound⟩ := exponential_tail_of_summationBound u hu hlim
    C c ε β D hC hc hε hεβ hβ1 hD hratioU hsum
  apply exponential_bound_all_positive_of_eventually a
    (fun n hn => lt_one_of_stretched_exponential_bound hc₀ hn (hdecay n hn))
  refine ⟨d,hd,?_⟩
  filter_upwards [hbound] with n hn
  have hau : a n ≤ u n :=
    le_mul_of_one_le_left (ha n) (Real.one_le_exp (Real.rpow_nonneg (Nat.cast_nonneg n) β))
  exact hau.trans hn

end PottsContinuity.Thm3.Prop4
