module

public import PottsContinuity.Thm3.Prop4.SplitWeight
public import PottsContinuity.Thm3.Prop4.UniformTail
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star

/-!
# The uniform weighted sum in Proposition 4

DCST, TeX lines 1775–1785: the uniform analytic-sum bound in the proof of Proposition 4.
The diagonal and off-diagonal terms are controlled separately. Every real
series used below is proved summable, including the actual tails.
-/

@[expose] public section

open Filter Topology

namespace PottsContinuity.Thm3.Prop4

/-- The actual finite split-weight convolution, with k+l=2m and both cutoffs. -/
noncomputable def prop4SplitWeight (ε β : ℝ) (m : ℕ) : ℝ := by
  classical
  exact ∑ k ∈ Finset.range (2*m+1),
    if (m : ℝ)^ε ≤ k ∧ (m : ℝ)^ε ≤ (2*m-k : ℕ) then
      Real.exp (-((k : ℝ)^β+((2*m-k : ℕ) : ℝ)^β)) else 0

/-- The exact nonnegative summand in the source's weighted tail. -/
noncomputable def prop4Kernel (C c ε β : ℝ) (m : ℕ) : ℝ :=
  C*(m : ℝ)^4*(Real.exp (c*(m : ℝ)^ε)*Real.exp (-2*(m : ℝ)^β)+
    c*(m : ℝ)^6*prop4SplitWeight ε β m)

/-- Nonnegativity holds at every index, including zero. -/
theorem prop4SplitWeight_nonneg (ε β : ℝ) (m : ℕ) : 0 ≤ prop4SplitWeight ε β m := by
  classical
  unfold prop4SplitWeight
  apply Finset.sum_nonneg
  intro k _
  split_ifs <;> positivity

/-- Nonnegativity of the actual kernel on its entire carrier. -/
theorem prop4Kernel_nonneg (C c ε β : ℝ) (hC : 0 ≤ C) (hc : 0 ≤ c) (m : ℕ) :
    0 ≤ prop4Kernel C c ε β m := by
  unfold prop4Kernel
  exact mul_nonneg (mul_nonneg hC (pow_nonneg (Nat.cast_nonneg m) _))
    (add_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      (mul_nonneg (mul_nonneg hc (pow_nonneg (Nat.cast_nonneg m) _))
        (prop4SplitWeight_nonneg ε β m)))

private theorem weighted_diagonal_identity (c ε β : ℝ) (m : ℕ) :
    Real.exp (((2*m : ℕ) : ℝ)^β)*Real.exp (c*(m : ℝ)^ε)*Real.exp (-2*(m : ℝ)^β) =
      Real.exp (c*(m : ℝ)^ε-(2-(2 : ℝ)^β)*(m : ℝ)^β) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Nat.cast_mul, Nat.cast_ofNat,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg m)]
  ring

/-- The weighted split convolution loses only one additional polynomial power. -/
theorem weighted_splitWeight_le {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (ε : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    Real.exp (((2*m : ℕ) : ℝ)^β)*prop4SplitWeight ε β m ≤
      (2*(m : ℝ)+1)*Real.exp (-(1-β)*(m : ℝ)^(ε*β)) := by
  have h := mul_le_mul_of_nonneg_left (split_exp_sum_le hβ hβ1 ε m hm)
    (Real.exp_nonneg (((2*m : ℕ) : ℝ)^β))
  change Real.exp (((2*m : ℕ) : ℝ)^β)*prop4SplitWeight ε β m ≤ _ at h
  have heq : Real.exp (((2*m : ℕ) : ℝ)^β)*
      ((2*(m : ℝ)+1)*Real.exp (-((2*m : ℕ) : ℝ)^β)*
        Real.exp (-(1-β)*(m : ℝ)^(ε*β))) =
      (2*(m : ℝ)+1)*Real.exp (-(1-β)*(m : ℝ)^(ε*β)) := by
    calc
      _ = (2*(m : ℝ)+1)*(Real.exp (((2*m : ℕ) : ℝ)^β)*
          Real.exp (-((2*m : ℕ) : ℝ)^β))*Real.exp (-(1-β)*(m : ℝ)^(ε*β)) := by ring
      _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]; ring
  exact h.trans_eq heq

/-- Explicit summable majorant for the source weighted kernel at positive indices. -/
theorem weighted_prop4Kernel_le (C c ε β : ℝ) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hβ : 0 < β) (hβ1 : β < 1) (m : ℕ) (hm : 1 ≤ m) :
    Real.exp (((2*m : ℕ) : ℝ)^β)*prop4Kernel C c ε β m ≤
      C*(m : ℝ)^4*Real.exp (c*(m : ℝ)^ε-(2-(2 : ℝ)^β)*(m : ℝ)^β)+
        (3*C*c)*(m : ℝ)^11*Real.exp (-(1-β)*(m : ℝ)^(ε*β)) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpoly : (m : ℝ)^4*(m : ℝ)^6*(2*(m : ℝ)+1) ≤ 3*(m : ℝ)^11 := by
    calc
      _ = (m : ℝ)^10*(2*(m : ℝ)+1) := by ring
      _ ≤ (m : ℝ)^10*(3*(m : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hmR]) (pow_nonneg (Nat.cast_nonneg m) _)
      _ = _ := by ring
  calc
    _ = C*(m : ℝ)^4*(Real.exp (((2*m : ℕ) : ℝ)^β)*
        Real.exp (c*(m : ℝ)^ε)*Real.exp (-2*(m : ℝ)^β))+
        C*c*(m : ℝ)^4*(m : ℝ)^6*(Real.exp (((2*m : ℕ) : ℝ)^β)*prop4SplitWeight ε β m) := by
      unfold prop4Kernel
      ring
    _ ≤ C*(m : ℝ)^4*Real.exp (c*(m : ℝ)^ε-(2-(2 : ℝ)^β)*(m : ℝ)^β)+
        C*c*(m : ℝ)^4*(m : ℝ)^6*((2*(m : ℝ)+1)*Real.exp (-(1-β)*(m : ℝ)^(ε*β))) := by
      rw [weighted_diagonal_identity]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (weighted_splitWeight_le hβ hβ1 ε m hm)
        (show 0 ≤ C*c*(m : ℝ)^4*(m : ℝ)^6 by positivity))
    _ = C*(m : ℝ)^4*Real.exp (c*(m : ℝ)^ε-(2-(2 : ℝ)^β)*(m : ℝ)^β)+
        (C*c*Real.exp (-(1-β)*(m : ℝ)^(ε*β)))*
          ((m : ℝ)^4*(m : ℝ)^6*(2*(m : ℝ)+1)) := by ring
    _ ≤ C*(m : ℝ)^4*Real.exp (c*(m : ℝ)^ε-(2-(2 : ℝ)^β)*(m : ℝ)^β)+
        (C*c*Real.exp (-(1-β)*(m : ℝ)^(ε*β)))*(3*(m : ℝ)^11) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hpoly
        (show 0 ≤ C*c*Real.exp (-(1-β)*(m : ℝ)^(ε*β)) by positivity))
    _ = _ := by ring

/-- Actual summability of the weighted source kernel. -/
theorem summable_weighted_prop4Kernel (C c ε β : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hε : 0 < ε) (hεβ : ε < β) (hβ1 : β < 1) :
    Summable (fun m : ℕ => Real.exp (((2*m : ℕ) : ℝ)^β)*prop4Kernel C c ε β m) := by
  have hβ : 0 < β := hε.trans hεβ
  have hd := summable_diagonal_weight 4 c (2-(2 : ℝ)^β) ε β hc
    (diagonal_rpow_gap_pos hβ1) hβ hεβ
  have ho := summable_rpow_mul_stretched_exp 11 (1-β) (ε*β)
    (sub_pos.mpr hβ1) (mul_pos hε hβ)
  have hmajor := (hd.mul_left C).add (ho.mul_left (3*C*c))
  apply hmajor.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _)
    (prop4Kernel_nonneg C c ε β hC.le hc.le m))]
  simpa only [Real.rpow_natCast, Real.rpow_ofNat, mul_assoc] using
    weighted_prop4Kernel_le C c ε β hC.le hc.le hβ hβ1 m hm

/-- Every actual source tail is summable, so no real-tsum default is being used. -/
theorem prop4Kernel_tail_summable (C c ε β : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hε : 0 < ε) (hεβ : ε < β) (hβ1 : β < 1) (n : ℕ) :
    Summable (fun m : {m : ℕ // n ≤ m} => prop4Kernel C c ε β m.1) := by
  apply summable_tail_of_weighted (prop4Kernel C c ε β)
    (fun m => Real.exp (((2*m : ℕ) : ℝ)^β))
    (prop4Kernel_nonneg C c ε β hC.le hc.le) ?_
    (summable_weighted_prop4Kernel C c ε β hC hc hε hεβ hβ1) n (Real.exp_pos _)
  intro k l hkl
  apply Real.exp_le_exp.mpr
  apply Real.rpow_le_rpow (by positivity) _ (hε.trans hεβ).le
  exact_mod_cast Nat.mul_le_mul_left 2 hkl

/-- The uniform analytic-sum bound in the proof of Proposition 4, with an explicit
positive finite upper bound uniform in n. The kernel expands to precisely the source's sum. -/
theorem prop4_analytic_sum_bound (C c ε β : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hε : 0 < ε) (hεβ : ε < β) (hβ1 : β < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      Real.exp (((2*n : ℕ) : ℝ)^β)*
        (∑' m : {m : ℕ // n ≤ m}, prop4Kernel C c ε β m.1) ≤ K := by
  let w : ℕ → ℝ := fun n => Real.exp (((2*n : ℕ) : ℝ)^β)
  have hw : Monotone w := by
    intro k l hkl
    apply Real.exp_le_exp.mpr
    apply Real.rpow_le_rpow (by positivity) _ (hε.trans hεβ).le
    exact_mod_cast Nat.mul_le_mul_left 2 hkl
  have hnonneg (m : ℕ) : 0 ≤ w m*prop4Kernel C c ε β m :=
    mul_nonneg (Real.exp_nonneg _) (prop4Kernel_nonneg C c ε β hC.le hc.le m)
  refine ⟨(∑' m : ℕ, w m*prop4Kernel C c ε β m)+1, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos (tsum_nonneg hnonneg) zero_lt_one
  · intro n _
    exact (weighted_tail_le_tsum (prop4Kernel C c ε β) w
      (prop4Kernel_nonneg C c ε β hC.le hc.le) (fun _ => Real.exp_nonneg _) hw
      (summable_weighted_prop4Kernel C c ε β hC hc hε hεβ hβ1) n).trans (by linarith)

end PottsContinuity.Thm3.Prop4
