module

public import PottsContinuity.Thm3.Prop4.WeightedDecay
public import Mathlib.Tactic

/-!
# The rounded, half-scale power cutoff

The source's even recursion has real lower threshold n^ε. Natural ceilings
retain this threshold exactly. Odd interpolation uses floor(n/2), as required
by the corrected argument.
-/

@[expose] public section

open Filter Topology

namespace PottsContinuity.Thm3.Prop4

/-- The natural index cutoff means the actual ceiling of the real power. -/
noncomputable def powerCutoff (ε : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ)^ε⌉₊

/-- The ceiling condition is precisely the real threshold at natural indices. -/
theorem powerCutoff_le_iff (ε : ℝ) (n k : ℕ) :
    powerCutoff ε n ≤ k ↔ (n : ℝ)^ε ≤ k := Nat.ceil_le

/-- Nonnegative powers give monotone rounded cutoffs. -/
theorem powerCutoff_monotone (ε : ℝ) (hε : 0 ≤ ε) : Monotone (powerCutoff ε) := by
  intro n m hnm
  exact Nat.ceil_mono (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnm) hε)

/-- Positive powers give diverging rounded cutoffs. -/
theorem powerCutoff_tendsto (ε : ℝ) (hε : 0 < ε) :
    Tendsto (powerCutoff ε) atTop atTop := by
  have hp := (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hp.eventually_ge_atTop (b : ℝ)] with n hn
  exact_mod_cast hn.trans (Nat.le_ceil ((n : ℝ)^ε))

/-- Integer half scales tend to infinity. -/
theorem halfIndex_tendsto : Tendsto (fun n : ℕ => n/2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (2*b)] with n hn
  omega

/-- The corrected rounded half-scale cutoff is eventually strictly below n. -/
theorem halfPowerCutoff_eventually_lt (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop, powerCutoff ε (n/2) < n := by
  have hpow := eventually_rpow_le_half_mul (α := 1) (β := ε) (c₀ := 1) hε1 zero_lt_one
  filter_upwards [hpow, eventually_ge_atTop 2] with n hn hn2
  have hcut : powerCutoff ε (n/2) ≤ powerCutoff ε n :=
    powerCutoff_monotone ε hε (Nat.div_le_self _ _)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hceil : powerCutoff ε n ≤ n-1 := by
    apply (powerCutoff_le_iff ε n (n-1)).mpr
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    simp only [Real.rpow_one] at hn
    exact hn.trans (by linarith)
  omega

end PottsContinuity.Thm3.Prop4
