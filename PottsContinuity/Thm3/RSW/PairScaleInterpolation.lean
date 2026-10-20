module

public import PottsContinuity.Thm3.RSW.AnnulusRecursion
public import PottsContinuity.Thm3.RSW.SquarePair

/-!
# Interpolating Proposition 3 between sevenfold scales

The exact reflected-FKG construction remains a separate geometric input:
a fixed positive integral power of a square-pair probability is bounded by the enclosing
annulus probability. This file performs the numerical interpolation only.
-/

@[expose] public section

namespace PottsContinuity.RSW

/-- Every integer beyond the initial scale lies immediately below a sevenfold
ladder scale, with a factor-seven gap. -/
theorem exists_sevenfold_scale_above (n₀ m : ℕ) (hn₀ : 1 ≤ n₀) (hm : n₀ ≤ m) :
    ∃ k : ℕ, m < 7^k*n₀ ∧ 7^k*n₀ ≤ 7*m := by
  have hnpos : 0 < n₀ := hn₀
  have hx : 1 ≤ m/n₀ := (Nat.le_div_iff_mul_le hnpos).mpr (by simpa using hm)
  obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near hx (by decide : 1 < (7:ℕ))
  refine ⟨k+1, (Nat.div_lt_iff_lt_mul hnpos).mp hk', ?_⟩
  have hlo : 7^k*n₀ ≤ m := (Nat.le_div_iff_mul_le hnpos).mp hk
  calc
    7^(k+1)*n₀ = 7*(7^k*n₀) := by rw [pow_succ]; ring
    _ ≤ 7*m := Nat.mul_le_mul_left 7 hlo

/-- Taking a positive integral root of an exponential power bound, with zero
values allowed. -/
theorem le_exp_of_pow_le_exp {a t : ℝ} (ha : 0 ≤ a) (p : ℕ) (hp : p ≠ 0)
    (h : a^p ≤ Real.exp t) : a ≤ Real.exp (t/(p:ℝ)) := by
  apply (pow_le_pow_iff_left₀ ha (Real.exp_nonneg _) hp).mp
  have hpR : (p:ℝ) ≠ 0 := by exact_mod_cast hp
  calc
    a^p ≤ Real.exp t := h
    _ = (Real.exp (t/(p:ℝ)))^p := by rw [← Real.exp_nat_mul, mul_div_cancel₀ _ hpR]

/-- The actual annulus ladder estimate implies square-pair stretched decay
at every scale beyond n₀, conditional on the reflected-FKG construction.
This is not an export of the construction itself. -/
theorem squarePair_eventual_decay_of_reflectedFKG
    (q : Set.Ici (1:ℝ)) (C d : ℝ) (hC : 1 ≤ C) (hd : 0 < d)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (p : ℕ) (hp : 0 < p)
    (hladder : ∀ k : ℕ,
      C*annulusProbability (selfDualParameters q) 8 (7^k*n₀) ≤
        Real.exp (-d*(((7^k*n₀:ℕ):ℝ)^sevenfoldExponent)))
    (hreflectedFKG : ∀ k m : ℕ, 1 ≤ m → m < 7^k*n₀ → 7^k*n₀ ≤ 7*m →
      (maxSquarePairProbability (selfDualParameters q) m)^p ≤
        annulusProbability (selfDualParameters q) 8 (7^k*n₀)) :
    ∀ m : ℕ, n₀ ≤ m → maxSquarePairProbability (selfDualParameters q) m ≤
      Real.exp (-(d/(p:ℝ))*(m:ℝ)^sevenfoldExponent) := by
  intro m hm
  obtain ⟨k, hmn, hnm⟩ := exists_sevenfold_scale_above n₀ m hn₀ hm
  have hpower : (maxSquarePairProbability (selfDualParameters q) m)^p ≤
      Real.exp (-d*(m:ℝ)^sevenfoldExponent) := by
    calc
      _ ≤ annulusProbability (selfDualParameters q) 8 (7^k*n₀) :=
        hreflectedFKG k m (hn₀.trans hm) hmn hnm
      _ ≤ C*annulusProbability (selfDualParameters q) 8 (7^k*n₀) :=
        le_mul_of_one_le_left (annulusProbability_nonneg _ _ _) hC
      _ ≤ Real.exp (-d*(((7^k*n₀:ℕ):ℝ)^sevenfoldExponent)) := hladder k
      _ ≤ _ := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left
          (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmn.le)
            sevenfoldExponent_pos.le) (neg_nonpos.mpr hd.le))
  have hroot := le_exp_of_pow_le_exp (maxSquarePairProbability_nonneg _ _) p (Nat.ne_of_gt hp) hpower
  convert hroot using 1
  congr 1
  ring

end PottsContinuity.RSW
